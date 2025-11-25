from itertools import combinations
# Use 'matroids' (small m) as requested
from sage.all import binomial, matroids, graphs, QQ, FreeAlgebra
from sage.matroids.advanced import *

# --- Part 1: SageMath Matroid ---
def get_cyclic_flats(M):
    cyclic_flats = []
    M_flats=[X for i in range(M.rank() + 1)
             for X in M.flats(i)]
    for F in M_flats:
        if not F:
            cyclic_flats.append(F)
            continue
        is_cyclic = True
        rk_F = M.rank(F)
        for x in F:
            if M.rank(F.difference([x])) < rk_F:
                is_cyclic = False
                break
        if is_cyclic:
            cyclic_flats.append(F)
    return cyclic_flats

def count_cyclic_flats(M, r, h):
    return sum(1 for F in get_cyclic_flats(M) if len(F) == h and M.rank(F) == r)

def count_modular_cyclic_pairs(M, alpha, beta, a, b):
    C = get_cyclic_flats(M)
    count = 0
    target_1 = (a, alpha) # (size_diff, rank_diff) for first part
    target_2 = (b, beta)  # (size_diff, rank_diff) for second part

    for F, G in combinations(C, 2):
        inter_len = len(F & G)

        # 1. Modularity Check
        if M.rank(F) + M.rank(G) != M.rank(F | G) + M.rank(F & G): 
            continue
        
        # 2. Compute parameters: (len(X) - len(I), rank(X) - len(I))
        pF = (len(F) - inter_len, M.rank(F) - inter_len)
        pG = (len(G) - inter_len, M.rank(G) - inter_len)

        # 3. Symmetric Check: Does {F, G} match {target_1, target_2}?
        if (pF == target_1 and pG == target_2) or (pF == target_2 and pG == target_1):
            count += 1
            
    return count


# --- Part 2: Symbolic cd-index ---
# Base ring
R = QQ
# Define Non-Commutative Algebras
NCA_ab = FreeAlgebra(R, 2, names=('a', 'b'))
NCA_cd = FreeAlgebra(R, 2, names=('c', 'd'))
a, b_ab = NCA_ab.gens() # Rename b to b_ab to avoid confusion
c_cd, d_cd = NCA_cd.gens()

# Define a Algebra to contain c, d, and b
# This is used for the intermediate calculations where 'b' appears
NCA_cdb = FreeAlgebra(R, 3, names=('c', 'd', 'b'))
c, d, b = NCA_cdb.gens()


# Memoization for the conversion rules
MEMO_MULTIPLIER = {}
MEMO_FINAL_TERM = {}

def convert_final_term(k):
    """
    Implements Rule 2: (a-b)^k -> cd-polynomial
    """
    if k in MEMO_FINAL_TERM:
        return MEMO_FINAL_TERM[k]

    if k < 0: return NCA_cdb(0)
    if k == 0: return NCA_cdb(1)

    base_squared = c*c - 2*d
    
    if k % 2 == 0: # Even powers
        res = base_squared**(k // 2)
    else: # Odd powers
        res = base_squared**((k - 1) // 2) * (c - 2*b)
    
    MEMO_FINAL_TERM[k] = res
    return res

def convert_multiplier(k):
    """
    Implements Rule 3: b*(a-b)^k -> cd-polynomial
    """
    if k in MEMO_MULTIPLIER:
        return MEMO_MULTIPLIER[k]

    # Base cases
    if k < 0: return NCA_cdb(0)
    if k == 0: return b # Returns 'b'
    if k == 1:
        # Rule for b*(a-b) -> d - cb
        res = d - c*b
        MEMO_MULTIPLIER[k] = res
        return res
    
    term1 = (c*c - 2*d) * convert_multiplier(k-2)
    term2 = (d*c - c*d) * convert_final_term(k-2)
    
    res = term1 + term2
    MEMO_MULTIPLIER[k] = res
    return res

# --- Formula 1: Hypersimplex---

def compute_hypersimplex_cd(k, n, memo=None):
    """
    Recursively computes the Psi_cd index for the Hypersimplex (Delta_k,n).
    """
    memo_key = ('hyp_cd', k, n)
    if memo is None: memo = {}
    if memo_key in memo: return memo[memo_key]

    if n <= 1:
        memo[memo_key] = NCA_cdb(0)
        return NCA_cdb(0)

    term1 = NCA_cdb(0)
    for i in range(k): # i=0..k-1
        comb_n_i = binomial(n, i) 
        if comb_n_i == 0: continue
        sum_j = NCA_cdb(0)
        j_start = max(0, 1 - i)
        for j in range(j_start, n - k): # j=j_start..n-k-1
            comb_ni_j = binomial(n - i, j)
            if comb_ni_j == 0: continue
            
            psi_recursive = compute_hypersimplex_cd(k - i, n - i - j, memo)
            
            pow_exp = i + j - 1
            if pow_exp < 0: continue
            multiplier_poly = convert_multiplier(pow_exp)
            sum_j += comb_ni_j * psi_recursive * multiplier_poly
            
        term1 += comb_n_i * sum_j

    pow_exp_2 = n - 2
    term2 = NCA_cdb(0)
    if pow_exp_2 >= 0:
        term2 = binomial(n, k) * convert_multiplier(pow_exp_2)

    pow_exp_3 = n - 1
    term3 = NCA_cdb(0)
    if pow_exp_3 >= 0:
        term3 = convert_final_term(pow_exp_3)

    total_index = term1 + term2 + term3
    memo[memo_key] = total_index
    return total_index

# --- Formula 2: General Hypersimplex Product ---

def compute_hypersimplex_product_cd(k, n, r, h, memo=None):
    """
    Computes Psi_cd(Delta_{k,n} x Delta_{r,h}) using a recursive formula.
    """
    memo_key = ('gen_prod_cd', k, n, r, h)
    if memo is None: memo = {}
    if memo_key in memo: return memo[memo_key]

    # --- Base Cases ---
    if n == 1 and (k == 1 or k == 0):
        res = compute_hypersimplex_cd(r, h, memo)
        memo[memo_key] = res
        return res

    if h == 1 and (r == 1 or r == 0):
        res = compute_hypersimplex_cd(k, n, memo)
        memo[memo_key] = res
        return res

    # --- Term 1: Proper faces ---
    term1 = NCA_cdb(0)
    for p in range(k): # p=0..k-1
        comb_n_p = binomial(n, p)
        if comb_n_p == 0: continue
        
        for q in range(r): # q=0..r-1
            comb_h_q = binomial(h, q)
            if comb_h_q == 0: continue
            
            # --- FIXED: i range(n-k) covers 0..n-k-1 ---
            for i in range(n - k): 
                comb_np_i = binomial(n - p, i)
                if comb_np_i == 0: continue
                
                j_start = max(0, 1 - i - p - q)
                j_end = h - r - 1
                
                for j in range(j_start, j_end + 1):
                    comb_hq_j = binomial(h - q, j)
                    if comb_hq_j == 0: continue
                    
                    psi_rec = compute_hypersimplex_product_cd(k - p, n - p - i, r - q, h - q - j, memo)
                    
                    pow_exp = p + q + i + j - 1
                    if pow_exp < 0: continue
                    multiplier_poly = convert_multiplier(pow_exp)
                    
                    term1 += comb_n_p * comb_h_q * comb_np_i * comb_hq_j * psi_rec * multiplier_poly

    # --- Term 2: Vertex x Face ---
    term2 = NCA_cdb(0)
    comb_nk = binomial(n, k)
    if comb_nk != 0:
        inner_sum2 = NCA_cdb(0)
        for i in range(r): # i=0..r-1
            comb_h_i = binomial(h, i)
            if comb_h_i == 0: continue
            
            j_start = 0 
            j_end = h - r - 1
            
            for j in range(j_start, j_end + 1):
                comb_hi_j = binomial(h - i, j)
                if comb_hi_j == 0: continue
                
                psi_delta_rec = compute_hypersimplex_cd(r - i, h - i - j, memo)
                
                pow_exp = i + j + n - 2
                if pow_exp < 0: continue
                multiplier_poly = convert_multiplier(pow_exp)
                
                inner_sum2 += comb_h_i * comb_hi_j * psi_delta_rec * multiplier_poly
        
        term2 = comb_nk * inner_sum2

    # --- Term 3: Face x Vertex ---
    term3 = NCA_cdb(0)
    comb_hr = binomial(h, r)
    if comb_hr != 0:
        inner_sum3 = NCA_cdb(0)
        for i in range(k): # i=0..k-1
            comb_n_i = binomial(n, i)
            if comb_n_i == 0: continue
            
            j_start = 0
            j_end = n - k - 1
            
            for j in range(j_start, j_end + 1):
                comb_ni_j = binomial(n - i, j)
                if comb_ni_j == 0: continue
                
                psi_delta_rec = compute_hypersimplex_cd(k - i, n - i - j, memo)
                
                pow_exp = i + j + h - 2
                if pow_exp < 0: continue
                multiplier_poly = convert_multiplier(pow_exp)
                
                inner_sum3 += comb_n_i * comb_ni_j * psi_delta_rec * multiplier_poly
        
        term3 = comb_hr * inner_sum3

    # --- Term 4: Empty chain ---
    term4 = NCA_cdb(0)
    pow_exp_4 = n + h - 2
    if pow_exp_4 >= 0:
        term4 = convert_final_term(pow_exp_4)

    # --- Term 5: Vertices ---
    term5 = NCA_cdb(0)
    pow_exp_5 = n + h - 3
    if pow_exp_5 >= 0:
        coeff = binomial(n, k) * binomial(h, r)
        term5 = coeff * convert_multiplier(pow_exp_5)

    total_index = term1 + term2 + term3 + term4 + term5
    memo[memo_key] = total_index
    return total_index


# --- Formula 3: P_Lambda (P_{\Lambda_{k-r,k,n-h,n}}) ---

def compute_P_Lambda_cd(k, n, r, h, memo=None):
    """
    Computes Psi_cd(P_Lambda_{k-r, k, n-h, n}) using the recursive formula.
    """
    memo_key = ('P_Lambda_cd', k, n, r, h)
    if memo is None: memo = {}
    if memo_key in memo: return memo[memo_key]
   # if k - r == n - h: return 0
  #  if k - r == 0: return 0
   #     total =                                            
   #     memo[memo_key] = total 
   #     return total

        
    
    # --- Term 1: Empty chian---
    term1 = convert_final_term(n - 1)
    
    # --- Term 2: Vertices ---
    term2_coeff = 0
    for i in range(r + 1): # i=0..r
        term2_coeff += binomial(h, i) * binomial(n - h, k - i)
    term2 = term2_coeff * convert_multiplier(n - 2)
    
    # --- Term 3: Proper face not in the Hyperplane ---
    term3 = NCA_cdb(0)
    for p in range(r): # p=0..h-1
        comb_k_p = binomial(h, p)
        if comb_k_p == 0: continue
        
        q_limit = (n - h) - (k - r) - 1
        for q in range(q_limit + 1): # q=0..limit (inclusive)
            comb_nh_q = binomial(n - h, q)
            if comb_nh_q == 0: continue
            
            i_limit = min(k - p - 1, n - h - q)
            for i in range(i_limit + 1): # i=0..limit
                comb_nhq_i = binomial(n - h - q, i)
                if comb_nhq_i == 0: continue
                
                j_start = max(0, 1 - p - q - i)
                j_limit = min(n - k - q - 1, h - p)
                for j in range(j_start, j_limit + 1): # j=start..limit
                    comb_hp_j = binomial(h - p, j)
                    if comb_hp_j == 0: continue
                    
                    if j >= h - r or i >= k - r:
                        u_k = k - p - i
                        u_n = n - i - j - p - q                         
                        psi_N = compute_hypersimplex_cd(u_k, u_n, memo)
                        
                    elif k == 1 or k == n - 1: continue 
                    else:
                        lam_k = k - p - i
                        lam_n = n - i - j - p - q
                        lam_r = r - p
                        lam_h = h - p - j
                        psi_N = compute_P_Lambda_cd(lam_k, lam_n, lam_r, lam_h,  memo)

                    pow_exp = p + q + i + j - 1
                    if pow_exp < 0: continue
                    multiplier_poly = convert_multiplier(pow_exp)
                    
                    
                    term3 += comb_k_p * comb_nh_q * comb_nhq_i * comb_hp_j * psi_N * multiplier_poly

    # --- Term 4: Faces in the Hyperplane ---
    psi_prod = compute_hypersimplex_product_cd(r, h, k - r, n - h, memo)
    term4 = psi_prod * (c - b) - term1 - (binomial(h, r) * binomial(n-h, k-r))*convert_multiplier(n - 2) #the last two things subtracsted are 

    total = term1 + term2 + term3 + term4                                                                #there to account the fact that we 
    memo[memo_key] = total                                                                               # are counting the empty and points
    return total

# --- NEW: Formula 4: Error term ---

def compute_W_formula(alpha, beta, a, b, n, memo=None):
    """
    Computes the formula for the error: W(alpha, beta, a, b) .
    """
    memo_key = ('W_formula', alpha, beta, a, b, n)
    if memo is None: memo = {}
    if memo_key in memo: return memo[memo_key]

    total_sum = NCA_cdb(0)
    for p in range(1, alpha + 1):
        
        for q in range(1, beta + 1):
            
            i_start = p + 1
            i_end = a - alpha + p
            
            for i in range(i_start, i_end + 1):
                j_start = q + 1
                j_end = b - beta + q
                
                for j in range(j_start, j_end + 1):
                    
                    # 1. Coefficient
                    c_ij = binomial(a, i) * binomial(b, j) * binomial(a - i, alpha - p) * binomial(b - j, beta - q)
                    if c_ij == 0: continue

                    # 2. Compute Psi_{cd}(Delta_{p,i} x Delta_{q,j}) using formula 2
                    psi_product = compute_hypersimplex_product_cd(p, i, q, j, memo)

                    # 3. Compute Psi_{cd}(Delta_{1, n-i-j}) using Formula 1
                    remaining_size = n - i - j
                    
                    # If remaining size < 1, the term is likely 0 (empty simplex)
                    if remaining_size < 1:
                        psi_simplex = NCA_cdb(0)
                    elif remaining_size == 1: #this is needed since previously we have assumed that cd-index of a point is zero for convenience.
                        psi_simplex = NCA_cdb(1)
                    else:
                        psi_simplex = compute_hypersimplex_cd(1, remaining_size, memo)

                    # 4. Combine terms
                    term = c_ij * psi_product * d * psi_simplex
                    
                    total_sum += term

    memo[memo_key] = total_sum
    return total_sum




# --- NEW: Formula 5: General Theorem ---

def calculate_general_formula(M):
    """
    Implements Theorem 4.6 for Connected Split Matroids.
    """
    #print(f"--- Analyzing Matroid M (Rank {M.rank()}, n={len(M.groundset())}) ---")

    # 1. Check Connectivity
    if not M.is_connected():
        print("Result: Matroid is NOT connected. Theorem 4.6 does not apply.")
        return None

   # print("Matroid is connected. Proceeding with General Formula...")

    # Parameters
    k = M.rank()
    n = len(M.groundset())
    memo = {}

    # --- Term 1: Base Hypersimplex ---
    term1 = compute_hypersimplex_cd(k, n, memo)

    # --- Term 2: Lambda Sum (Cyclic Flats) ---
    # Sum over 0 < r < h < n
    term2_sum = NCA_cdb(0)
    
    # Loop r from 1 to k-1 
    # Loop h from r+1 to n-1.
    for r in range(1, k): 
        for h in range(r + 1, n):
            
            # Get lambda(r, h)
            lam_val = count_cyclic_flats(M, r, h)
            
            
            if lam_val > 0:
                psi_lambda = compute_P_Lambda_cd(k, n, r, h, memo)
                psi_delta = compute_hypersimplex_cd(k, n, memo)
                
                term2_sum += lam_val * (psi_lambda - psi_delta)

    # --- Term 3: Error Term---
    
    term3_sum = NCA_cdb(0)
    
    for a in range(2, n):
        for alpha in range(1, a): # 0 < alpha < a
            
            for b in range(2, n):
                for beta in range(1, b): # 0 < beta < b
                    
                    # Check Lexicographical Order: (alpha, a) <= (beta, b)
                    if (alpha < beta) or (alpha == beta and a <= b):
                        mu_val = count_modular_cyclic_pairs(M, alpha, beta, a, b)
                        
                        if mu_val > 0:
                            w_val = compute_W_formula(alpha, beta, a, b, n, memo)
                            term3_sum += mu_val * w_val


    # --- Final Result ---
    total_index = term1 + term2_sum - term3_sum
    return total_index
# --- Part 3: Main Execution Block ---

if __name__ == "__main__":
    M1= BasisMatroid(groundset='abcdef', nonbases=['ab', 'ac','ad', 'bc','bd', 'cd' ])
    M2= BasisMatroid(groundset='abcdef', nonbases=['ab', 'ac', 'bc','de' ])
    M3= BasisMatroid(groundset='abcdef', nonbases=['ab', 'cd','ef'])
    U26 = matroids.Uniform(2,6)
    N1= BasisMatroid(groundset='abcdefg', nonbases=['ab', 'ac','ad','ae', 'bc','bd', 'be', 'cd', 'ce', 'de' ])
    N2= BasisMatroid(groundset='abcdefg', nonbases=['ab', 'ac','ad', 'bc','bd', 'cd', 'ef'])
    N3= BasisMatroid(groundset='abcdefg', nonbases=['ab', 'ac', 'bc','de', 'df', 'ef'])
    N4= BasisMatroid(groundset='abcdefg', nonbases=['ab', 'ac', 'bc' , 'de', 'fg'])
    F = matroids.catalog.Fano()
    V = matroids.catalog.Vamos()
    fra1 = calculate_general_formula(M1)
    fra2 = calculate_general_formula(M2)
    fra3 = calculate_general_formula(M3)
    uni26 = calculate_general_formula(U26)
    bro1 = calculate_general_formula(N1)
    bro2 = calculate_general_formula(N2)
    bro3 = calculate_general_formula(N3)
    bro4 = calculate_general_formula(N4)
    fano = calculate_general_formula(F)
    vamos = calculate_general_formula(V)
    print(f"Result general formula M1: {fra1}")
    print(f"Result general formula M2: {fra2}")
    print(f"Result general formula M3: {fra3}")
    print(f"Result general formula U2,6: {uni26}")
    print(f"Result general formula N1: {bro1}")
    print(f"Result general formula N2: {bro2}")
    print(f"Result general formula N3: {bro3}")
    print(f"Result general formula N4: {bro4}")
    print(f"Result general formula Fano: {fano}")
    print(f"Result general formula Vamos: {vamos}")
