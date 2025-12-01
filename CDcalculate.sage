import sqlite3
import pickle
import os
from itertools import combinations
from sage.all import binomial, matroids, graphs, QQ, FreeAlgebra
from sage.matroids.advanced import *

# --- Part 0: Database Management ---

class CdIndexDB:
    def __init__(self, db_name="cd_index_cache_fast.db"):
        self.db_name = db_name
        self.conn = sqlite3.connect(self.db_name, check_same_thread=False)
        self.create_tables()

    def create_tables(self):
        cur = self.conn.cursor()
        cur.execute('''
            CREATE TABLE IF NOT EXISTS hypersimplex (
                k INTEGER, n INTEGER, poly BLOB, PRIMARY KEY (k, n)
            )
        ''')
        cur.execute('''
            CREATE TABLE IF NOT EXISTS lambda_poly (
                k INTEGER, n INTEGER, r INTEGER, h INTEGER, poly BLOB, PRIMARY KEY (k, n, r, h)
            )
        ''')
        cur.execute('''
            CREATE TABLE IF NOT EXISTS product_poly (
                k INTEGER, n INTEGER, r INTEGER, h INTEGER, poly BLOB, PRIMARY KEY (k, n, r, h)
            )
        ''')
        self.conn.commit()
        cur.close()

    def _blob_to_obj(self, blob):
        if blob is None: return None
        return pickle.loads(blob)

    def _obj_to_blob(self, obj):
        return sqlite3.Binary(pickle.dumps(obj))

    def _get_generic(self, query, params):
        cur = self.conn.cursor()
        try:
            # FIX: Converto tutti i parametri in int standard Python
            safe_params = tuple(int(x) if hasattr(x, 'ndigits') or hasattr(x, 'is_integer') else x for x in params)
            cur.execute(query, safe_params)
            row = cur.fetchone()
            return self._blob_to_obj(row[0]) if row else None
        finally:
            cur.close()

    def _save_generic(self, query, params):
        cur = self.conn.cursor()
        try:
            # FIX: Converto tutti i parametri (tranne il BLOB finale) in int standard Python
            # params[:-1] sono i numeri, params[-1] è il BLOB
            numbers = [int(x) for x in params[:-1]]
            blob = params[-1]
            safe_params = tuple(numbers + [blob])
            
            cur.execute(query, safe_params)
            self.conn.commit()
        except sqlite3.Error as e:
            print(f"DB Error: {e}")
        finally:
            cur.close()

    # --- Hypersimplex ---
    def get_hypersimplex(self, k, n):
        return self._get_generic("SELECT poly FROM hypersimplex WHERE k=? AND n=?", (k, n))

    def save_hypersimplex(self, k, n, poly_obj):
        self._save_generic("INSERT OR REPLACE INTO hypersimplex VALUES (?, ?, ?)", 
                           (k, n, self._obj_to_blob(poly_obj)))

    # --- Lambda ---
    def get_lambda(self, k, n, r, h):
        return self._get_generic("SELECT poly FROM lambda_poly WHERE k=? AND n=? AND r=? AND h=?", (k, n, r, h))

    def save_lambda(self, k, n, r, h, poly_obj):
        self._save_generic("INSERT OR REPLACE INTO lambda_poly VALUES (?, ?, ?, ?, ?)", 
                           (k, n, r, h, self._obj_to_blob(poly_obj)))

    # --- Product ---
    def get_product(self, k, n, r, h):
        return self._get_generic("SELECT poly FROM product_poly WHERE k=? AND n=? AND r=? AND h=?", (k, n, r, h))

    def save_product(self, k, n, r, h, poly_obj):
        self._save_generic("INSERT OR REPLACE INTO product_poly VALUES (?, ?, ?, ?, ?)", 
                           (k, n, r, h, self._obj_to_blob(poly_obj)))

    def close(self):
        self.conn.close()

DB_MANAGER = CdIndexDB()

# --- Part 1: SageMath Matroid ---
def get_cyclic_flats(M):
    cyclic_flats = []
    M_flats=[X for i in range(M.rank() ) for X in M.flats(i)]
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

def get_cyclic_flat_counts_vector(M):
    counts = {}
    n = len(M.groundset())
    cyclic_flats = get_cyclic_flats(M) # Calcolato una volta sola

    for F in cyclic_flats:
        h = len(F)
        r = M.rank(F)
        
        # Vincoli richiesti: 0 < r < h < n
        # Nota: se h < n, allora F != GroundSet, quindi r < M.rank() è implicito
        if 0 < r < h < n:
            key = (r, h)
            counts[key] = counts.get(key, 0) + 1
            
    return counts

def get_modular_cyclic_pairs_vector(M):
    counts = {}
    n = len(M.groundset())
    C = get_cyclic_flats(M) # Calcolato una volta sola
    
    for F, G in combinations(C, 2):
        # r(F) + r(G) = r(F U G) + r(F n G)
        inter_FG = F.intersection(G)
        union_FG = F.union(G)
        
        rF = M.rank(F)
        rG = M.rank(G)
        
        r_union = M.rank(union_FG)
        r_inter = M.rank(inter_FG)
        
        if rF + rG != r_union + r_inter:
            continue
            
        # --- 2. Calcolo Parametri ---
        len_inter = len(inter_FG)
        
        # Parametri per F (potenziale candidato 1)
        a = len(F) - len_inter
        alpha = rF - r_inter
        
        # Parametri per G (potenziale candidato 2)
        b = len(G) - len_inter
        beta = rG - r_inter
        
        # 0 < alpha < a < n  AND  0 < beta < b < n
        if not (0 < alpha < a < n): continue
        if not (0 < beta < b < n): continue
        
        # Dobbiamo assicurare (alpha, a) <= (beta, b)
        p1 = (alpha, a)
        p2 = (beta, b)
        
        if p1 <= p2:
            # L'ordine è già corretto (o sono uguali)
            key = (alpha, beta, a, b)
        else:
            # Scambiamo per rispettare l'ordine lessicografico
            # p2 diventa la parte "alpha", p1 la parte "beta"
            key = (beta, alpha, b, a)
            
        counts[key] = counts.get(key, 0) + 1

    return counts

# --- Part 2: Symbolic cd-index ---
R = QQ
NCA_ab = FreeAlgebra(R, 2, names=('a', 'b'))
NCA_cd = FreeAlgebra(R, 2, names=('c', 'd'))
a, b_ab = NCA_ab.gens()
c_cd, d_cd = NCA_cd.gens()

# Global Algebra for calculation
NCA_cdb = FreeAlgebra(R, 3, names=('c', 'd', 'b'))
c, d, b = NCA_cdb.gens()


MEMO_MULTIPLIER = {}
MEMO_FINAL_TERM = {}

def convert_final_term(k):
    if k in MEMO_FINAL_TERM: return MEMO_FINAL_TERM[k]
    if k < 0: return NCA_cdb(0)
    if k == 0: return NCA_cdb(1)
    base_squared = c*c - 2*d
    if k % 2 == 0: res = base_squared**(k // 2)
    else: res = base_squared**((k - 1) // 2) * (c - 2*b)
    MEMO_FINAL_TERM[k] = res
    return res

def convert_multiplier(k):
    if k in MEMO_MULTIPLIER: return MEMO_MULTIPLIER[k]
    if k < 0: return NCA_cdb(0)
    if k == 0: return b
    if k == 1:
        res = d - c*b
        MEMO_MULTIPLIER[k] = res
        return res
    term1 = (c*c - 2*d) * convert_multiplier(k-2)
    term2 = (d*c - c*d) * convert_final_term(k-2)
    res = term1 + term2
    MEMO_MULTIPLIER[k] = res
    return res

# --- Formula 1: Hypersimplex (With Pickle DB) ---

def compute_hypersimplex_cd(k, n, memo=None):
    memo_key = ('hyp_cd', k, n)
    if memo is None: memo = {}
    #print(f"{k,n}")
    # 1. Check RAM
    if memo_key in memo: return memo[memo_key]

    # 2. Check Database (Restituisce direttamente l'oggetto Sage o None)
    cached_poly = DB_MANAGER.get_hypersimplex(k, n)
    if cached_poly is not None:
        memo[memo_key] = cached_poly
        return cached_poly

    # Calcolo...
    if n <= 1:
        res = NCA_cdb(0)
        memo[memo_key] = res
        return res

    term1 = NCA_cdb(0)
    for i in range(k):
        comb_n_i = binomial(n, i) 
        if comb_n_i == 0: continue
        sum_j = NCA_cdb(0)
        j_start = max(0, 1 - i)
        for j in range(j_start, n - k):
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
    
    # 3. Save to RAM and Database (Passiamo l'oggetto, il DB manager farà il pickle)
    memo[memo_key] = total_index
    DB_MANAGER.save_hypersimplex(k, n, total_index)
    
    return total_index

# --- Formula 2: General Hypersimplex Product (With Pickle DB) ---

def compute_hypersimplex_product_cd(k, n, r, h, memo=None):
    memo_key = ('gen_prod_cd', k, n, r, h)
    if memo is None: memo = {}
    
    if memo_key in memo: return memo[memo_key]

    cached_poly = DB_MANAGER.get_product(k, n, r, h)
    if cached_poly is not None:
        memo[memo_key] = cached_poly
        return cached_poly

    if n == 1 and (k == 1 or k == 0):
        res = compute_hypersimplex_cd(r, h, memo)
        memo[memo_key] = res
        return res

    if h == 1 and (r == 1 or r == 0):
        res = compute_hypersimplex_cd(k, n, memo)
        memo[memo_key] = res
        return res

    term1 = NCA_cdb(0)
    for p in range(k):
        comb_n_p = binomial(n, p)
        if comb_n_p == 0: continue
        for q in range(r):
            comb_h_q = binomial(h, q)
            if comb_h_q == 0: continue
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

    term2 = NCA_cdb(0)
    comb_nk = binomial(n, k)
    if comb_nk != 0:
        inner_sum2 = NCA_cdb(0)
        for i in range(r):
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

    term3 = NCA_cdb(0)
    comb_hr = binomial(h, r)
    if comb_hr != 0:
        inner_sum3 = NCA_cdb(0)
        for i in range(k):
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

    term4 = NCA_cdb(0)
    pow_exp_4 = n + h - 2
    if pow_exp_4 >= 0:
        term4 = convert_final_term(pow_exp_4)

    term5 = NCA_cdb(0)
    pow_exp_5 = n + h - 3
    if pow_exp_5 >= 0:
        coeff = binomial(n, k) * binomial(h, r)
        term5 = coeff * convert_multiplier(pow_exp_5)

    total_index = term1 + term2 + term3 + term4 + term5
    #print(f"prod: {r,h, k, n}")   
    
    memo[memo_key] = total_index
    DB_MANAGER.save_product(k, n, r, h, total_index)
    return total_index

# --- Formula 3: P_Lambda (With Pickle DB) ---

def compute_P_Lambda_cd(k, n, r, h, memo=None):
    memo_key = ('P_Lambda_cd', k, n, r, h)
    if memo is None: memo = {}
    
    if memo_key in memo: return memo[memo_key]

    cached_poly = DB_MANAGER.get_lambda(k, n, r, h)
    if cached_poly is not None:
        memo[memo_key] = cached_poly
        return cached_poly

    term1 = convert_final_term(n - 1)
    
    term2_coeff = 0
    for i in range(r + 1):
        term2_coeff += binomial(h, i) * binomial(n - h, k - i)
    term2 = term2_coeff * convert_multiplier(n - 2)
    
    term3 = NCA_cdb(0)
    for p in range(r):
        comb_k_p = binomial(h, p)
        if comb_k_p == 0: continue
        q_limit = (n - h) - (k - r) - 1
        for q in range(q_limit + 1):
            comb_nh_q = binomial(n - h, q)
            if comb_nh_q == 0: continue
            i_limit = min(k - p - 1, n - h - q)
            for i in range(i_limit + 1):
                comb_nhq_i = binomial(n - h - q, i)
                if comb_nhq_i == 0: continue
                j_start = max(0, 1 - p - q - i)
                j_limit = min(n - k - q - 1, h - p)
                for j in range(j_start, j_limit + 1):
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

    psi_prod = compute_hypersimplex_product_cd(r, h, k - r, n - h, memo)
    term4 = psi_prod * (c - b) - term1 - (binomial(h, r) * binomial(n-h, k-r))*convert_multiplier(n - 2)

    total = term1 + term2 + term3 + term4    
    #print(f"lambda: {r,h, k, n}")                                                
    
    memo[memo_key] = total
    DB_MANAGER.save_lambda(k, n, r, h, total)
    return total

# --- Formula 4: Error term (Invariato, usa memo e le altre funzioni cachate) ---

def compute_W_formula(alpha, beta, a, b, n, memo=None):
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
                    c_ij = binomial(a, i) * binomial(b, j) * binomial(a - i, alpha - p) * binomial(b - j, beta - q)
                    if c_ij == 0: continue
                    psi_product = compute_hypersimplex_product_cd(p, i, q, j, memo)
                    remaining_size = n - i - j
                    if remaining_size < 1: psi_simplex = NCA_cdb(0)
                    elif remaining_size == 1: psi_simplex = NCA_cdb(1)
                    else: psi_simplex = compute_hypersimplex_cd(1, remaining_size, memo)
                    term = c_ij * psi_product * d * psi_simplex
                    total_sum += term

    memo[memo_key] = total_sum
    return total_sum

# --- Formula 5: General Theorem ---

def calculate_general_formula(M):
    if not M.is_connected():
        print(f"Matroid {M} is NOT connected.")
        return None

    k = M.rank()
    n = len(M.groundset())
    memo = {}

    # --- Termine 1: Ipersimplesso base ---
    term1 = compute_hypersimplex_cd(k, n, memo)

    # --- Termine 2: Somma sui Cyclic Flats (lambda) ---
    term2_sum = NCA_cdb(0)
    
    # Generiamo il vettore sparso dei conteggi
    lambda_counts = get_cyclic_flat_counts_vector(M)
    
    # Iteriamo solo sulle coppie (r, h) che esistono effettivamente
    for (r, h), lam_val in lambda_counts.items():
        # I vincoli 0 < r < h < n sono già garantiti dalla funzione di conteggio
        psi_lambda = compute_P_Lambda_cd(k, n, r, h, memo)
        psi_delta = compute_hypersimplex_cd(k, n, memo)
        term2_sum += lam_val * (psi_lambda - psi_delta)
        #print(f"{r,h, lam_val}")

    # --- Termine 3: Somma sulle Coppie Modulari (mu) ---
    term3_sum = NCA_cdb(0)
    
    # Generiamo il vettore sparso dei conteggi delle coppie
    pair_counts = get_modular_cyclic_pairs_vector(M)
    
    # Iteriamo solo sulle tuple (alpha, beta, a, b) esistenti
    for (alpha, beta, a, b), mu_val in pair_counts.items():
        # I vincoli lessicografici e di range sono già garantiti
        w_val = compute_W_formula(alpha, beta, a, b, n, memo)
        term3_sum += mu_val * w_val
        #print(f"{alpha, beta, a, b, w_val}")

    total_index = term1 + term2_sum - term3_sum
    return total_index

if __name__ == "__main__":
    S1= BasisMatroid(groundset='abcdef', nonbases=['ab', 'ac','ad', 'bc','bd', 'cd' ])
    S2= BasisMatroid(groundset='abcdef', nonbases=['ab', 'ac', 'bc','de' ])
    S3= BasisMatroid(groundset='abcdef', nonbases=['ab', 'cd','ef'])
    N1= BasisMatroid(groundset='abcdefg', nonbases=['ab', 'ac','ad','ae', 'bc','bd', 'be', 'cd', 'ce', 'de' ])
    N2= BasisMatroid(groundset='abcdefg', nonbases=['ab', 'ac','ad', 'bc','bd', 'cd', 'ef'])
    N3= BasisMatroid(groundset='abcdefg', nonbases=['ab', 'ac', 'bc','de', 'df', 'ef'])
    N4= BasisMatroid(groundset='abcdefg', nonbases=['ab', 'ac', 'bc' , 'de', 'fg'])
    M1 = BasisMatroid(groundset='abcdefgh', nonbases=['abcd', 'abef' ])
    M2 = BasisMatroid(groundset='abcdefgh', nonbases=['abcd', 'aefg'])
    M3 = BasisMatroid(groundset='abcdefgh', nonbases=['abcd', 'efgh'])
    F = matroids.catalog.Fano()
    V = matroids.catalog.Vamos()
    fra1 = calculate_general_formula(S1)
    fra2 = calculate_general_formula(S2)
    fra3 = calculate_general_formula(S3)
    bro1 = calculate_general_formula(N1)
    bro2 = calculate_general_formula(N2)
    bro3 = calculate_general_formula(N3)
    bro4 = calculate_general_formula(N4)
    ex1 = calculate_general_formula(M1)
    ex2 = calculate_general_formula(M2)
    ex3 = calculate_general_formula(M3)
    fano = calculate_general_formula(F)
    vamos = calculate_general_formula(V)
    print(f"Result general formula S1: {fra1}")
    print(f"Result general formula S2: {fra2}")
    print(f"Result general formula S3: {fra3}")
    print(f"Result general formula N1: {bro1}")
    print(f"Result general formula N2: {bro2}")
    print(f"Result general formula N3: {bro3}")
    print(f"Result general formula N4: {bro4}")
    print(f"Result general formula M1: {ex1}")
    print(f"Result general formula M2: {ex2}")
    print(f"Result general formula M3: {ex3}")
    print(f"Result general formula Fano: {fano}")
    print(f"Result general formula Vamos: {vamos}")
    """"" This can be run only if you download the SageMath matroid database


    for M in matroids.AllMatroids(6, 3):
        if M.is_connected(): #connceted
            C = get_cyclic_flats(M)
            s = sum(1 for F,G in combinations(C, 2) if F < G and F != frozenset() and G != frozenset(range(6))) #split
            if s == 0:
                res = calculate_general_formula(M)
                print(f"Result general formula: {res}")
                print(M)
    """""
