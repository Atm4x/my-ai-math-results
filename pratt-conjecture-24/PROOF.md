# A radix-seven construction of superlinear cyclic ETF value

## 1. Statement

Let $\operatorname{val}(G)$ be the maximum number of zero-sum triples in an equilateral trapezoid-free (ETF) triple of subsets of a finite abelian group $G$. In additive notation, ETF means that, for fixed anchors in the appropriate roles, each system

$$
0=a'+b+c=a+b'+c,\qquad
0=a'+b+c=a+b+c',\qquad
0=a+b'+c=a+b+c'
$$

has at most one solution $(a,b,c)$ in the three subsets. This is Definition 17 of Kevin Pratt, [*On Generalized Corners and Matrix Multiplication*](https://doi.org/10.4230/LIPIcs.ITCS.2024.89), ITCS 2024, p. 89:9; Conjecture 24, p. 89:11.

**Theorem.** For $k=8m$, $m\ge1$, put $N_k=3(7^k-1)+1$. Then

$$
\operatorname{val}(\mathbb Z_{N_k})\ge\frac{(8m)!}{(m!)^8}.
$$

In particular, along these moduli,

$$
\operatorname{val}(\mathbb Z_{N_k})
=\Omega\left(N_k^{\log_7 8}/(\log N_k)^{7/2}\right).
$$

This disproves the bound asserted in Conjecture 24, provided the construction and its interpretation survive independent review.

## 2. Digit certificate

Set $A=\{0,1,2,4\}$, $B=\{0,1,2,3,4,5,6\}$, $C=\{0,1,5,6\}$. Let $Y$ be the induced relation $a+b+c=6$ in $A\times B\times C$. Select the following eight edges $X\subset Y$:

| a | b | c |
|--:|--:|--:|
| 0 | 0 | 6 |
| 0 | 5 | 1 |
| 0 | 6 | 0 |
| 1 | 0 | 5 |
| 2 | 3 | 1 |
| 2 | 4 | 0 |
| 4 | 1 | 1 |
| 4 | 2 | 0 |

The other three edges of $Y$ are $(0,1,5),(1,4,1),(1,5,0)$.

The selected relation is linear (two coordinates uniquely determine the third). Its ETF property follows from the following neighbor tables: for each center, take the Cartesian product of its two neighbor sets. Within each table, distinct centers have disjoint rectangles.

| A-center | B-neighbors | C-neighbors |
|--:|:--|:--|
| 0 | 0,5,6 | 0,1,6 |
| 1 | 0 | 5 |
| 2 | 3,4 | 0,1 |
| 4 | 1,2 | 0,1 |

| B-center | A-neighbors | C-neighbors |
|--:|:--|:--|
| 0 | 0,1 | 5,6 |
| 1 | 4 | 1 |
| 2 | 4 | 0 |
| 3 | 2 | 1 |
| 4 | 2 | 0 |
| 5 | 0 | 1 |
| 6 | 0 | 0 |

| C-center | A-neighbors | B-neighbors |
|--:|:--|:--|
| 0 | 0,2,4 | 2,4,6 |
| 1 | 0,2,4 | 1,3,5 |
| 5 | 1 | 0 |
| 6 | 0 | 0 |

Indeed, fixed anchors in two roles lie in at most one rectangle belonging to the third role; linearity then determines both remaining unknowns. This is the anchored uniqueness property in each orientation.

Define weights $u(1)=1$, $v(0)=-2$, $w(5)=1$, $w(6)=2$, and set every other weight in its respective role to zero. On $Y$, the sum $u(a)+v(b)+w(c)$ is zero on $X$ and one on the three other edges, as direct substitution shows.

**Important:** $Y$ itself is not ETF. The next step removes its additional edges at the level of induced sets, rather than assuming that a chosen non-induced subrelation is a valid witness.

## 3. Fixed marginal types and no carries

Fix $m\ge1$, $k=8m$, and $h=7^k-1$. Construct three sets $A_k,B_k,C_k$ of integers by encoding length-$k$ radix-seven words whose digit multiplicities are the following (multiply each listed multiplicity by $m$):

| Role | Multiplicities |
| --- | --- |
| A | 0:3, 1:1, 2:2, 4:2 |
| B | 0:2, 1:1, 2:1, 3:1, 4:1, 5:1, 6:1 |
| C | 0:3, 1:3, 5:1, 6:1 |

Encoding sends a digit word to $\sum_{i=0}^{k-1} d_i7^i$; it is injective for fixed length. All encoded values lie in $[0,h]$.

For any induced target $a+b+c=h$, the three digit masses are $13m,21m,14m$, totaling $6k$. The carries satisfy $q_0=q_k=0$, $q_i\ge0$, and

$$
a_i+b_i+c_i+q_i=6+7q_{i+1}.
$$

Summing over $i$ gives $6\sum_{i=1}^{k-1}q_i=0$. Thus every carry is zero and every coordinate triple belongs to $Y$.

The marginal types also force the sum of all weights to be $m-4m+3m=0$. Each coordinate weight is either zero or one; therefore every coordinate weight is zero. Every coordinate triple belongs to $X$.

## 4. ETF and target count

For fixed anchors in any pair of roles, both equations of the corresponding anchored system are induced target equations. By Section 3, both hold coordinatewise in $X$. The ETF uniqueness of $X$ implies at most one solution in each coordinate, hence at most one full solution. This proves ETF for the induced integer relation.

Each ordered sequence containing $m$ copies of each of the eight selected digit edges encodes a target. Distinct sequences encode distinct triples. Conversely, every induced target consists of edges of $X$; the multiplicities of digits $1,\ldots,6$ of $B$ fix the counts of six edges, and those of digits 5 and 6 of $C$ fix the other two. Thus the number of targets is exactly

$$
T_k=\frac{(8m)!}{(m!)^8}.
$$

## 5. Cyclic embedding and asymptotics

Take $N_k=3h+1$. Map $A_k,B_k$ into $\mathbb Z_{N_k}$ by reduction modulo $N_k$, and map $C_k$ by translation by $-h$ followed by reduction. The maps are injective. For $a,b,c\in[0,h]$, the only multiple of $N_k$ in the range of $a+b+c-h\in[-h,2h]$ is zero. Thus every modular target equation is equivalent to its integer counterpart, including the equations in all three anchored systems. ETF and target count are preserved.

Stirling's formula gives $T_k=\Theta(8^k/k^{7/2})$, while $N_k=\Theta(7^k)$. This proves the claimed lower bound. For any fixed $0<\varepsilon<\log_7 8-1$, the ratio $\operatorname{val}(\mathbb Z_{N_k})/N_k^{1+\varepsilon}$ tends to infinity, contradicting Conjecture 24.

## 6. Reproducibility and formal proof

The finite certificate and factorial inequalities at $k=112,120$ can be checked using [verify_seed.py](verify_seed.py). The general argument does not depend on these experiments.

The accompanying [Lean development](lean/Pratt.lean) proves an alternative all-length lower bound with a polynomial loss $(6n+1)^6$, using pigeonholing rather than Stirling's formula, and formally negates the necessary natural-power version of Conjecture 24. See [the formalization notes](lean/README.md) for the precise correspondence. The sharper multinomial estimate above is an informal proof, not a claim that the exact Stirling bound appears in Lean.

Independent external review and scientific priority verification remain pending.
