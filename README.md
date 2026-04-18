# A Factorization Result for Palindromic $0-1$ Polynomials

This repository contains a Lean 4 formalization of the theorem below. The theorem
is known in the literature, intent of this repository is to provide it's formal verification.

## Definitions

For a polynomial

$$
f(x)=\sum_{i=0}^d a_i x^i
$$

of degree $d$, its *reciprocal polynomial* is

$$
f^\ast(x)=x^d f(1/x).
$$

We call $f$ a $0-1$ *polynomial* if $a_i\in\lbrace 0,1\rbrace$ for all $i$, and
*palindromic* if $a_i=a_{d-i}$ for $0\le i\le d$; equivalently, if

$$
f^\ast=f.
$$

## Theorem

Let $P$ and $Q$ be monic polynomials with nonnegative real coefficients.
If $R(x)=P(x)Q(x)$ is a palindromic $0-1$ polynomial, then $P$ and $Q$ are
also palindromic $0-1$ polynomials.

## Formal Proof

The machine-checked Lean 4 proof is in [Proof.lean](Proof.lean).

It can be validated with:

```sh
lake build
```

The command should finish without errors when the formalization is valid. On
the first run it may also download the Lean toolchain and the pinned `mathlib4`
dependency.

## Informal Proof

The following proof is inspired by a proof for polynomials of the form $x^k+\cdots+x+1$.
See references below.

Write $P = \sum p_k x^k$, $Q = \sum q_k x^k$, $R = PQ$, $m = \deg P$,
$n = \deg Q$. Assume without loss of generality that $m \le n$; the
case $m = 0$ is trivial, since then $P = 1$ and $Q = R$. Palindromic
symmetry means $R_k = R_{m+n-k}$ throughout. Monicity gives
$p_m = q_n = 1$, hence $R_{m+n} = 1$.

It is convenient to picture the coefficients of $PQ$ through the
$(m{+}1)\times(n{+}1)$ grid of pairwise products $p_i q_j$; the
coefficient $R_k$ is then the sum along the anti-diagonal $i+j=k$.
The four extreme corners of this grid, and the two anti-diagonals at
$i+j=m$ and $i+j=n$, are the only geometric features used below.

```
              q_0   q_1   q_2   ...   q_{n-1}   q_n
            +----------------------------------------+
   p_0      |  *     .     .    ...     .         *  |
            |                                        |
   p_1      |  .     .     .    ...     .         .  |
            |                                        |
    :       |              .                         |
            |                                        |
   p_{m-1}  |  .     .     .    ...     .         .  |
            |                                        |
   p_m      |  *     .     .    ...     .         *  |
            +----------------------------------------+
```

Cell $(i, j)$ holds the product $p_i q_j$; the coefficient $R_k$ is
the sum along the anti-diagonal $i + j = k$. The four starred corners
are the singleton diagonals $R_0 = p_0 q_0$ and $R_{m+n} = p_m q_n$,
together with the two extreme terms $p_m q_0$ (in the anti-diagonal
$R_m$) and $p_0 q_n$ (in the anti-diagonal $R_n$); these are all
equal to $1$ after Step 1. Step 2 focuses on the two anti-diagonals
$i+j=m$ and $i+j=n$ (running from corner $(0,m)$ to $(m,0)$ and from
$(0,n)$ to $(m,n-m)$ respectively), whose sums $R_m$ and $R_n$ must
agree by palindromicity.

### Step 1 (corner coefficients)

From $R_0 = R_{m+n} = 1$ we get $p_0 q_0 = 1$. The $i = 0$ summand of
$R_n = \sum_i p_i q_{n-i}$ equals $p_0 q_n = p_0$, and every summand
is non-negative, so $p_0 \le R_n \le 1$; symmetrically $q_0 \le 1$.
With $p_0 q_0 = 1$ and $p_0, q_0 > 0$, this forces $p_0 = q_0 = 1$.

### Step 2 (diagonal constraints)

Since $p_i = 0$ for $i > m$, expanding around the boundary terms,

$$
\begin{aligned}
R_m &= 1 + q_m + S_1,       & S_1 &:= \sum_{i=1}^{m-1} p_i q_{m-i}, \\\\
R_n &= 1 + q_{n-m} + S_2,   & S_2 &:= \sum_{i=1}^{m-1} p_i q_{n-i},
\end{aligned}
$$

with every summand $\ge 0$. The palindromic identity $R_m = R_n$
together with $R_m, R_n \in \\{0, 1\\}$ forces the common value to be
$1$ (otherwise $m = n$ would make it $\ge 2$); hence $m < n$ and

$$
q_m \\;=\\; q_{n-m} \\;=\\; 0, \qquad S_1 \\;=\\; S_2 \\;=\\; 0.
$$

In particular, for every $1 \le i \le m - 1$,

$$
p_i q_{m-i} \\;=\\; 0 \qquad \text{and} \qquad p_i q_{n-i} \\;=\\; 0. \qquad (\dagger)
$$

### Step 3 (inward induction)

We prove by strong induction on $k$, for $0 \le k \le \lfloor m/2 \rfloor$,

$$
p_k, q_k \in \\{0, 1\\}, \qquad p_k = p_{m-k}, \qquad q_k = q_{n-k}. \qquad (\*)
$$

The base case $k = 0$ is immediate. For $k \ge 1$, peel off the
boundary terms:

$$
\begin{aligned}
R_k &= p_k + q_k + T,           & T  &:= \sum_{i=1}^{k-1} p_i q_{k-i}, \\\\
R_{m+n-k} &= p_{m-k} + q_{n-k} + T', & T' &:= \sum_{i=m-k+1}^{m-1} p_i q_{m+n-k-i}.
\end{aligned}
$$

The substitution $j = m - i$, together with the inductive symmetries
$p_{m-j} = p_j$ and $q_{n-k+j} = q_{k-j}$, shows $T' = T$.
Palindromicity $R_k = R_{m+n-k}$ then yields

$$
p_k + q_k \\;=\\; p_{m-k} + q_{n-k}. \qquad (\ddagger)
$$

Every factor in $T$ is in $\\{0, 1\\}$ by the induction hypothesis,
so $T \in \mathbb{Z}_{\ge 0}$. Since $R_k = T + p_k + q_k \in \\{0,1\\}$
and $p_k + q_k \ge 0$, we have $p_k + q_k \in \\{0, 1\\}$.

If $p_k + q_k = 0$, non-negativity and $(\ddagger)$ give
$p_k = q_k = p_{m-k} = q_{n-k} = 0$, so $(\*)$ holds.

If $p_k + q_k = 1$, the bounds $1 \le k \le m-1$ and
$1 \le m-k \le m-1$ permit applying $(\dagger)$ at $i = k$ and $i = m-k$:

$$
p_k q_{n-k} \\;=\\; 0, \qquad p_{m-k} q_k \\;=\\; 0.
$$

If $q_{n-k} = 0$, then $(\ddagger)$ forces $p_{m-k} = 1$; hence
$p_{m-k} q_k = 0$ gives $q_k = 0$, so $p_k = 1$. If $q_{n-k} \ne 0$,
then $p_k = 0$, so $q_k = 1$; then $p_{m-k} q_k = 0$ forces
$p_{m-k} = 0$, and $(\ddagger)$ gives $q_{n-k} = 1$. Either way,
$(\*)$ holds at $k$.

### Step 4 ($P$ is a palindromic $0–1$ polynomial)

By $(\*)$, $p_k \in \\{0, 1\\}$ for $k \le \lfloor m/2 \rfloor$; the
identity $p_k = p_{m-k}$ extends this to $k \le m$. Since $p_k = 0$
for $k > m$, $P$ has coefficients in $\\{0, 1\\}$, and the same
identity gives palindromicity.

### Step 5 ($Q$ has $0–1$ coefficients)

By Step 4, $P \in \mathbb{Z}[x]$ and is monic, and
$R \in \mathbb{Z}[x]$ by hypothesis. Polynomial long division over
$\mathbb{Z}$ — which succeeds because $P$ has leading coefficient $1$
— yields $Q = R/P \in \mathbb{Z}[x]$. Combined with the hypothesis
that $Q$ has non-negative coefficients, $q_k \in \mathbb{Z}_{\ge 0}$
for every $k$.

For each $k$, using $p_0 = 1$ from Step 1 and non-negativity of all
summands,

$$
R_k \\;=\\; p_0 q_k + \sum_{i \ge 1} p_i q_{k-i} \\;\ge\\; q_k.
$$

Hence $q_k \le R_k \le 1$, and $q_k \in \mathbb{Z}_{\ge 0}$ forces
$q_k \in \\{0, 1\\}$.

### Step 6 ($Q$ is palindromic)

Let $\widetilde{P}$ denote the reverse of $P$. Since
$P(0) = p_0 = 1 \ne 0$ and $P$ is palindromic, $\widetilde{P} = P$;
similarly $R(0) = 1 \ne 0$ and $\widetilde{R} = R$. In the integral
domain $\mathbb{R}[x]$ one has
$\widetilde{R} = \widetilde{P} \cdot \widetilde{Q} = P \cdot \widetilde{Q}$;
combined with $\widetilde{R} = R = P \cdot Q$ and cancelling
$P \ne 0$, we obtain $\widetilde{Q} = Q$, i.e., $Q$ is palindromic.
$\blacksquare$

## References

- M. Krasner and H. Ranulac (1937), *Sur une propriété des polynomes de la
  division du cercle*, *C. R. Acad. Sci. Paris* 204, 397-399.
- D. Raikov, *Sur une propriété des polynômes de la division du cercle*, **Rec. Math. [Mat. Sbornik] 
  N.S.** 2(44):2 (1937), 379–382. [Math-Net.Ru](https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=sm&paperid=5576&option_lang=eng)
- The theorem formalized here is a special palindromic case of the broader
  conjecture discussed in the MathOverflow question
  [Why do polynomials with coefficients 0,1 like to have only factors with 0,1 coefficients?](https://mathoverflow.net/questions/339137).
