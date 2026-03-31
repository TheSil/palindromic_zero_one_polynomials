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

Write

$$
P(x)=\sum_{i=0}^m p_i x^i,
\qquad
Q(x)=\sum_{j=0}^n q_j x^j
$$

and

$$
R(x)=P(x)Q(x)=\sum_{k=0}^{m+n} r_k x^k.
$$

Since $P$ and $Q$ are monic, we have

$$
p_m=q_n=1.
$$

After swapping $P$ and $Q$ if necessary, assume $m\le n$.

If $m=0$, then $P=1$, hence $Q=R$, and the conclusion is immediate. Thus we may
assume

$$
m>0.
$$

Because $R$ is monic and palindromic, its constant term equals its leading
coefficient, so

$$
r_0=r_{m+n}=1.
$$

The diagonal $k=n$ contains the term

$$
p_0q_n=p_0,
$$

hence

$$
p_0\le r_n\le 1.
$$

Similarly, the diagonal $k=m$ contains the term

$$
p_mq_0=q_0,
$$

so

$$
q_0\le r_m\le 1.
$$

Since

$$
r_0=p_0q_0=1,
$$

it follows that

$$
p_0=q_0=1.
$$

For each $k$,

$$
r_k=\sum_{i+j=k} p_i q_j.
$$

All summands are nonnegative and $r_k\le 1$, so every product $p_iq_j$
appearing in such a sum satisfies

$$
p_i q_j \le 1.
$$

We first show that $m<n$. Indeed, if $m=n>0$, then the coefficient $r_m$
contains the two distinct terms

$$
p_0 q_m = q_m = 1,
\qquad
p_m q_0 = 1,
$$

so $r_m\ge 2$, impossible. Hence $m<n$.

Now consider the diagonal $k=m$. It contains the terms

$$
p_0 q_m = q_m
\qquad\text{and}\qquad
p_m q_0 = 1,
$$

so

$$
r_m \ge q_m+1.
$$

Since $r_m\le 1$, it follows that

$$
q_m=0,
\qquad
r_m=1,
$$

and all the other terms on that diagonal must vanish:

**(1)**

$$
p_i q_{m-i}=0
\qquad
(1\le i\le m-1).
$$

By palindromicity,

$$
r_n=r_m=1.
$$

The diagonal $k=n$ contains the terms

$$
p_0 q_n=1
\qquad\text{and}\qquad
p_m q_{n-m}=q_{n-m},
$$

hence

$$
q_{n-m}=0,
$$

and again all remaining terms on that diagonal vanish:

**(2)**

$$
p_i q_{n-i}=0
\qquad
(1\le i\le m-1).
$$

We claim, by induction on $k=0,1,\dots,\lfloor m/2\rfloor$, that

$$
p_k,p_{m-k},q_k,q_{n-k}\in\lbrace 0,1\rbrace,
\qquad
p_k=p_{m-k},
\qquad
q_k=q_{n-k}.
$$

For $k=0$, this is exactly the normalization

$$
p_0=p_m=q_0=q_n=1.
$$

Assume the claim holds for all smaller indices, and fix $k\ge 1$. Set

$$
S=\sum_{i=1}^{k-1} p_i q_{k-i}.
$$

By the induction hypothesis, every term in this sum is either $0$ or $1$, so
$S$ is a nonnegative integer. We have

$$
r_k = p_k + q_k + S.
$$

Similarly,

$$
r_{m+n-k}=p_{m-k}+q_{n-k}+S',
$$

where

$$
S'=\sum_{i=1}^{k-1} p_{m-i} q_{\,n-k+i}.
$$

By the induction hypothesis,

$$
p_{m-i}=p_i
\qquad\text{and}\qquad
q_{\,n-k+i}=q_{k-i},
$$

so $S'=S$. Since $R$ is palindromic,

$$
r_k=r_{m+n-k},
$$

and therefore

$$
p_k+q_k=p_{m-k}+q_{n-k}=:T.
$$

Because

$$
T=r_k-S,
$$

and $r_k\in\lbrace 0,1\rbrace$ while $S$ is a nonnegative integer, we have

$$
T\in\lbrace 0,1\rbrace.
$$

If $T=0$, then

$$
p_k=q_k=p_{m-k}=q_{n-k}=0.
$$

Now suppose $T=1$. Then

**(3)**

$$
p_k+q_k=1,
\qquad
p_{m-k}+q_{n-k}=1.
$$

Also, by **(2)** and **(1)**,

**(4)**

$$
p_k q_{n-k}=0,
\qquad
p_{m-k} q_k=0.
$$

Using **(3)**, we may write

$$
q_k=1-p_k,
\qquad
q_{n-k}=1-p_{m-k}.
$$

Substituting into **(4)**, we get

$$
p_k(1-p_{m-k})=0,
\qquad
p_{m-k}(1-p_k)=0.
$$

If $p_k=1$, then the first equation gives $p_{m-k}=1$. If $p_k<1$, then the
second equation gives $p_{m-k}=0$, and then the first equation forces $p_k=0$.
Thus

$$
p_k=p_{m-k}\in\lbrace 0,1\rbrace,
$$

and then **(3)** yields

$$
q_k=q_{n-k}=1-p_k\in\lbrace 0,1\rbrace.
$$

This completes the induction. In particular, $p_k=p_{m-k}$ for
$0\le k\le \lfloor m/2\rfloor$, and therefore $P$ is palindromic. Also every
coefficient of $P$ lies in $\lbrace 0,1\rbrace$: indeed, for any index $t$, either
$t\le \lfloor m/2\rfloor$ or $m-t\le \lfloor m/2\rfloor$, so the induction
covers all coefficients.

It remains to treat $Q$. Suppose some coefficient of $Q$ is not in $\lbrace 0,1\rbrace$,
and let $i$ be minimal with this property. Then

$$
q_i\in(0,1).
$$

By minimality,

$$
q_0,\dots,q_{i-1}\in\lbrace 0,1\rbrace,
$$

while we already know all coefficients of $P$ lie in $\lbrace 0,1\rbrace$. Therefore in

$$
r_i=q_i+\sum_{a=1}^{\min(m,i)} p_a q_{i-a},
$$

the sum

$$
N:=\sum_{a=1}^{\min(m,i)} p_a q_{i-a}
$$

is a nonnegative integer. Hence

$$
q_i=r_i-N
$$

is an integer, contradicting $q_i\in(0,1)$.

Therefore every coefficient of $Q$ also lies in $\lbrace 0,1\rbrace$.

Finally, since $P$ and $R$ are palindromic, we have

$$
P^\ast=P,
\qquad
R^\ast=R.
$$

Because $P$ and $Q$ are monic, reversing the identity $R=PQ$ gives

$$
R^\ast=P^\ast Q^\ast.
$$

Hence

$$
PQ = R = R^\ast = P^\ast Q^\ast = P Q^\ast.
$$

Since $P\neq 0$, cancellation in $\mathbb{R}[x]$ yields

$$
Q=Q^\ast.
$$

Thus $Q$ is palindromic.

So both $P$ and $Q$ are palindromic $0-1$ polynomials.

## References

- M. Krasner and H. Ranulac (1937), *Sur une propriété des polynomes de la
  division du cercle*, *C. R. Acad. Sci. Paris* 204, 397-399.
- D. Raikov, *Sur une propriété des polynômes de la division du cercle*, **Rec. Math. [Mat. Sbornik] 
  N.S.** 2(44):2 (1937), 379–382. [Math-Net.Ru](https://www.mathnet.ru/php/archive.phtml?wshow=paper&jrnid=sm&paperid=5576&option_lang=eng)
- The theorem formalized here is a special palindromic case of the broader
  conjecture discussed in the MathOverflow question
  [Why do polynomials with coefficients 0,1 like to have only factors with 0,1 coefficients?](https://mathoverflow.net/questions/339137).
