
  


## Definitions
  
 A case-lambda is **non-exhaustive** if-and-only-if there is at least one valid input which results in the symbol *'no-match* being returned. Note that to evaluate exhaustiveness, it suffices to examine the parameter types and the list of pattern vectors; the return types and the templates can be ignored.

So let's consider non-exhaustiveness as a predicate taking a single input; an *m*-by-*n* **match matrix** of patterns, where *m* is the number of cases and *n* is the number of parameters.

*Note: For the examples below, consider the following type declaration:*
```racket
(data Any
      true
      false
      (box Any)
      (pair Any Any))
```
  
**An example 5-by-1 match matrix, M:**

| Any |
|:-------------:|
| (pair _ true) |
| (pair true _) |
| (box _)       |
| true          |
| false         |

*Note that we're appending an additional header row to represent the type of that column, and that _ represents a wildcard pattern variable. Is this matrix exhaustive?*



## Hints & Preliminary considerations:

  

1. **Consider Compliments:** Note that we are defining non-exhaustiveness instead of exhaustiveness. You are welcome to proceed either way, but the logic of the former case is almost certainly simpler.

2. **Order Doesn't Matter:** Note that, unlike in the general problem of matching, the order of rows doesn't matter for determining exhaustiveness. Thus we are free to reorder rows, or more usefully, to consider related subsets of rows independently of one-another.

3. **Go Wild, Forget Your Names:** Recall that our patterns are linear; that is, a given pattern variable can only occur once in a given pattern. Recall as well that exhaustiveness testing doesn't actually require binding any variables. This means that pattern variables can be considered homogeneously. In other words, if we solve the problem for patterns using only a single generic wildcard (_), the full solution is only a trivial generalization.

4. **Forget Types (for now):** Similarly, the core of the problem is the same regardless of type information. We suggest that you first solve the problem without types; that is, for a fixed set of constructors, when every constructor can occur as argument to any other. Generalising this solution will require substantial but straightforward modification.

5. **Resist the Urge to Collapse:** While it may seem simpler to start with one-argument functions, don't do this to the point of forgetting the multi-column case. While it definitely makes sense to begin by thinking about one-argument functions and sets of only nullary constructors, you'll find that as soon as you begin considering constructors taking two or more variables, something resembling the multi-column case creeps in whether you invited it or not!

6. **Reflect on Recursion:** It's a fair bet that solving this problem will involve some casework. The easiest way to manage this is probably recursive reduction. That is, given a match matrix **M**, we suggest defining a recursive function **NE(M)** to implement our non-exhaustiveness predicate. Implementing NE will likely involve breaking down M into one or more simpler matrices, and calling NE on them recursively. Our goal is to move towards base cases whose exhaustiveness (or lack thereof is obvious). Since we're dealing with a matrix where each entry is a complex nested data type, note that we can simplify the matrix by either :

		a. Reducing the number of columns
		b. Reducing the number of rows
		c. Reducing the nesting depth in one or more entries.


 
 ## Sketch of an Algorithm


Proceed recursively, considering a single column at a time. Call the first column of the matrix C, and define the *signature* of C to be the set of all constructors which are the head of a pattern in C. We say this signature is *complete* if it consists of every constructor (of the relevant type).  In our **example M above**, this set is {*true*, *false*, *box*, *pair*}, which is the complete signature for type *Any*.

**Case 1:** The signature is complete. In this case, we can consider each constructor independently. That is, we can separate our matrix into submatrices for every constructor in our signature. If **any** of these is non-exhaustive, then the original matrix is non-exhaustive. Note that since every entry in the first column of these submatrices will be the same constructor, we can just drop those constructors and instead append their arguments as new columns. This probably sounds confusing; see the examples below, in particular the *pair* example. Note that while, for each submatrix, we're dropping the rows whose first entries are headed by other constructors, we do need to be careful with how we handle rows headed by wildcards. This doesn't occur in our example, so you should work out a similar case yourself whose first column does have both a complete signature and a wildcard.

**CASE1(M, true) == CASE1(M, false), 1-by-0 match matrices:**

| (empty row) |
|:-----------:|
| (empty row) |

**CASE1(M, box), a 1-by-1 match matrix:**

|  Any |
|:----:|
| _    |

**CASE1(M, pair), a 2 by 2 match matrix:**

| Any  | Any  |
|:-----|-----:|
| _    | true |
| true | _    |

The box case is clearly exhaustive. The true/false cases looks a bit weird, but semantically we know these should be fine, suggesting we might consider a matrix consisting of an empty row to be exhaustive. On the other hand, the pair case seems more suspect, so let's continue. 

**Case 2**: The signature is not complete. If this is the case, clearly we'll have to rely on wildcards. If there are none in the column, then we're stuck, and the match matrix is non-exhaustive. If there are wildcards, then we can always ensure a match for this variable, so we can discard the first column and proceed to consider the rest. BUT this means that we've committed to this wildcard, and so before proceeding we should discard all rows which *don't* begin with a wildcard.

Note that CASE1(M, pair) above is such a matrix, since the signature of its first column is just {true}. So we discard the non-wildcard rows and the first column to form:

**CASE2(CASE1(M,cons)), a 1-by-1 matrix:**

| Any  |
|------|
| true |

This matrix is clearly non-exhaustive, so by the rules for Case 1, the original matrix M is non-exhaustive. In the interests of homogeneity, note that this is again a case-2 matrix. Discarding all non-wildcard rows yields the empty matrix, suggesting that we treat the empty matrix (as distinct from a matrix with an empty row, as above) as non-exhaustive.
