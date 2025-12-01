# cd-index-matroid-base-polytope
# **How to Use CALCULATOR\_cd.sage**

This script is version 0.2 of a program that calculates the **cd-index** of connected matroids using SageMath. It includes a built-in caching system (SQLite) to speed up repeated calculations of hypersimplices, products of hypersimplices and Schubert matroids.

## **1\. Prerequisites**

You need **SageMath** installed on your system.

* **Mac/Linux:** Usually available via command line (sage).  
* **Windows:** Use the SageMath shell or WSL.

## **2\. How to Run the Script**

There are two main ways to use this file:

### **Option A: Run as a Standalone Script**

If you just want to see the results for the matroids defined in the code (at the bottom), run this command in your terminal:  
sage CALCULATOR\_cd.sage

### **Option B: Interactive Mode **

This is best if you want to define new matroids on the fly without editing the file every time.

1. Open your terminal and type sage to enter the SageMath shell.  
2. Load the script:  
   load("CALCULATOR\_cd.sage")

3. Now you can use the functions directly. For example:  
   \# Define a matroid via Basis. (Many other options avaliable)  
   M1 \= BasisMatroid(groundset='abc', bases=\['ab', 'ac'\] )

   \# Calculate the cd-index  
   result \= calculate\_general\_formula(M1)  
   print(result)

## **3\. How to Compute Your Own Matroids**

To calculate the cd-index for your specific matroids, you have two choices:

### **Method 1: Edit the File**

Scroll to the bottom of CALCULATOR\_cd.sage to the if \_\_name\_\_ \== "\_\_main\_\_": block. You can add your own definitions there:  
if \_\_name\_\_ \== "\_\_main\_\_":  
    \# ... existing code ...  
      
    \# 1\. Define your matroid (e.g., from bases)  
    \# Rank 3 on groundset {0,1,2,3,4,5} with specific non-bases  
    MyMatroid \= BasisMatroid(groundset='012345', nonbases=\['01', '02', '23'\])  
      
    \# 2\. Calculate  
    res \= calculate\_general\_formula(MyMatroid)  
    print(f"Result for MyMatroid: {res}")

### **Method 2: Use SageMath Catalog**

SageMath has a built-in library of matroids you can test immediately:  
\# In the Sage shell or script:  
F \= matroids.catalog.Fano()  
V \= matroids.catalog.Vamos()  
print(calculate\_general\_formula(F))  
print(calculate\_general\_formula(V))

## **4\. Understanding the Database (Cache)**

The script creates a file named cd\_index\_cache\_fast.db in the same directory.

* **What it does:** It saves the results of some fundamental calculations (hypersimplices, products of hypersimplices and Schubert matroids).  
* **Benefit:** If you run the code again or compute a larger matroid that uses smaller common substructures, it will run much faster.  
* **How to start:** You can start immediately with your favorite matroids by downloading our database called “cd\_index\_cache\_fast.db” from GitHub.

## **5\. Outputs**

* **"Matroid from Kim10":** The matroids S1, S2, S3 and N1, N2, N3, N4 are the matroids of rank two with three parallelism classes described by Sangwook Kim in TABLE 1 at the end of his paper “FLAG ENUMERATIONS OF MATROID BASE POLYTOPES”. This shows that our formula is basically a generalization of his formula that completes the cases he was missing.  
* **Our examples:** M1, M2 and M3 are the examples presented in the extended abstract.  
* **Classical:** F and V are the famous Fano and Vamos matroids.

## **6\. Errata**

N.B. This version of the program corrects a sign error present in version 0.1. An extended abstract of the corresponding article reports results computed with version 0.1, thus the output is wrong. The correct output is given by version 0.2 onwards.
