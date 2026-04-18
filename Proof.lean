import Mathlib

open Finset Polynomial
open scoped BigOperators

namespace ZeroOnePolyPalindromicCase

def IsZeroOnePoly (p : ℝ[X]) : Prop :=
  ∀ k : ℕ, p.coeff k = 0 ∨ p.coeff k = 1

def HasNonnegCoeffs (p : ℝ[X]) : Prop :=
  ∀ k : ℕ, 0 ≤ p.coeff k

def IsPalindromic (p : ℝ[X]) : Prop :=
  ∀ k : ℕ, k ≤ p.natDegree → p.coeff k = p.coeff (p.natDegree - k)

def conv (p q : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), p i * q (k - i)

lemma coeff_mul_eq_conv (P Q : ℝ[X]) (k : ℕ) :
    (P * Q).coeff k = conv P.coeff Q.coeff k := by
  rw [Polynomial.coeff_mul]
  simpa [conv] using
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ P.coeff i * Q.coeff j) k)

lemma mul_eq_zero_or_one {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a * b = 0 ∨ a * b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

lemma exists_natCast_eq_sum_of_zero_one {s : Finset ℕ} {f : ℕ → ℝ}
    (hf : ∀ i ∈ s, f i = 0 ∨ f i = 1) :
    ∃ t : ℕ, (t : ℝ) = ∑ i ∈ s, f i := by
  classical
  exact ⟨(s.filter fun i ↦ f i = 1).card,
    (Finset.natCast_card_filter (R := ℝ) (p := fun i ↦ f i = 1) s).trans
      (Finset.sum_congr rfl fun i hi ↦ by rcases hf i hi with h | h <;> simp [h])⟩

lemma eq_zero_or_one_of_nonneg_add_natCast_eq_zero_or_one {x : ℝ} {t : ℕ}
    (hx : 0 ≤ x) (h : x + (t : ℝ) = 0 ∨ x + (t : ℝ) = 1) :
    x = 0 ∨ x = 1 := by
  rcases h with h | h
  · exact Or.inl ((add_eq_zero_iff_of_nonneg hx (Nat.cast_nonneg t)).1 h).1
  · have : t ≤ 1 := by exact_mod_cast (show (t : ℝ) ≤ 1 by linarith)
    interval_cases t <;> simp_all

lemma conv_decomp {p q : ℕ → ℝ} {k : ℕ} (hk : 0 < k) :
    conv p q k =
      (∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1))) + p k * q 0 + p 0 * q k := by
  unfold conv
  rw [Finset.sum_range_succ' (f := fun i ↦ p i * q (k - i)),
    show k = (k - 1) + 1 from by omega, Finset.sum_range_succ]
  simp [show (k - 1) + 1 = k from by omega]

lemma conv_at_degree_right_decomp {p q : ℕ → ℝ} {m n : ℕ}
    (hm0 : 0 < m) (hmn : m < n) (hp_support : ∀ i, m < i → p i = 0) :
    conv p q n =
      (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (n - (i + 1))) + p m * q (n - m) + p 0 * q n := by
  unfold conv
  rw [show n + 1 = (m + 1) + (n - m) from by omega,
    Finset.sum_range_add (f := fun i ↦ p i * q (n - i))]
  have htail : (∑ i ∈ Finset.range (n - m), p (m + 1 + i) * q (n - (m + 1 + i))) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by rw [hp_support _ (by omega), zero_mul]
  rw [htail, add_zero, Finset.sum_range_succ' (f := fun i ↦ p i * q (n - i)),
    show m = (m - 1) + 1 from by omega, Finset.sum_range_succ]
  simp [show (m - 1) + 1 = m from by omega]

lemma conv_high_decomp {p q : ℕ → ℝ} {m n k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ m) (hmn : m ≤ n)
    (hp_support : ∀ i, m < i → p i = 0) (hq_support : ∀ i, n < i → q i = 0) :
    conv p q (m + n - k) =
      (∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1))) +
        p m * q (n - k) + p (m - k) * q n := by
  -- Step 1: reduce conv to a finite sum over range (k + 1) using supports of p and q.
  have hstep :
      conv p q (m + n - k) = ∑ i ∈ Finset.range (k + 1), p (m - k + i) * q (n - i) := by
    unfold conv
    rw [show m + n - k + 1 = (m - k) + (n + 1) from by omega,
      Finset.sum_range_add (f := fun i ↦ p i * q (m + n - k - i))]
    have hhead : (∑ i ∈ Finset.range (m - k), p i * q (m + n - k - i)) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        rw [hq_support _ (by have := Finset.mem_range.mp hi; omega), mul_zero]
    rw [hhead, zero_add]
    simp_rw [show ∀ i, m + n - k - (m - k + i) = n - i from fun i ↦ by omega]
    rw [show n + 1 = (k + 1) + (n - k) from by omega,
      Finset.sum_range_add (f := fun i ↦ p (m - k + i) * q (n - i))]
    have htail : (∑ i ∈ Finset.range (n - k), p (m - k + (k + 1 + i)) * q (n - (k + 1 + i))) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ by rw [hp_support _ (by omega), zero_mul]
    rw [htail, add_zero]
  -- Step 2: peel off boundary terms and reflect the middle sum.
  rw [hstep, Finset.sum_range_succ' (f := fun i ↦ p (m - k + i) * q (n - i))]
  simp only [Nat.sub_zero, add_zero]
  have hk' : (k - 1) + 1 = k := by omega
  rw [← hk', Finset.sum_range_succ, hk', show m - k + k = m from by omega]
  congr 1; congr 1
  rw [← Finset.sum_range_reflect
    (fun i ↦ p (m - (i + 1)) * q (n - k + (i + 1))) (k - 1)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi_lt := Finset.mem_range.mp hi
  simp only [show (k - 1) - 1 - i + 1 = k - 1 - i from by omega,
    show m - (k - 1 - i) = m - k + (i + 1) from by omega,
    show n - k + (k - 1 - i) = n - (i + 1) from by omega]

lemma constant_coeffs_one_of_palindromic_zero_one_ordered {P Q : ℝ[X]}
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPnonneg : HasNonnegCoeffs P) (hQnonneg : HasNonnegCoeffs Q)
    (hpal : IsPalindromic (P * Q)) (h01 : IsZeroOnePoly (P * Q)) :
    P.coeff 0 = 1 ∧ Q.coeff 0 = 1 := by
  have hdegPQ : (P * Q).natDegree = P.natDegree + Q.natDegree := hPmonic.natDegree_mul hQmonic
  have htop : (P * Q).coeff (P.natDegree + Q.natDegree) = 1 := by
    simpa [hdegPQ] using (hPmonic.mul hQmonic).coeff_natDegree
  have hR0 : (P * Q).coeff 0 = 1 := by
    simpa [IsPalindromic, hdegPQ, htop] using hpal 0 (Nat.zero_le _)
  have hprod : P.coeff 0 * Q.coeff 0 = 1 := by
    simpa [Polynomial.mul_coeff_zero] using hR0
  -- When B is monic and both A, B have nonneg coefficients, A.coeff 0 ≤ (A * B).coeff B.natDegree
  -- (the i = 0 term of the convolution gives A(0) · B(natDeg B) = A(0) · 1).
  have bound : ∀ {A B : ℝ[X]}, B.Monic → HasNonnegCoeffs A → HasNonnegCoeffs B →
      A.coeff 0 ≤ (A * B).coeff B.natDegree := by
    intro A B hB hAnn hBnn
    rw [coeff_mul_eq_conv]; unfold conv
    simpa [Nat.sub_zero, hB.coeff_natDegree, mul_one] using
      (Finset.single_le_sum (s := Finset.range (B.natDegree + 1)) (a := 0)
        (f := fun i ↦ A.coeff i * B.coeff (B.natDegree - i))
        (fun i _ ↦ mul_nonneg (hAnn i) (hBnn _)) (by simp))
  have hP0_le_coeff : P.coeff 0 ≤ (P * Q).coeff Q.natDegree := bound hQmonic hPnonneg hQnonneg
  have hQ0_le_coeff : Q.coeff 0 ≤ (P * Q).coeff P.natDegree := by
    rw [mul_comm]; exact bound hPmonic hQnonneg hPnonneg
  have hP0_le : P.coeff 0 ≤ 1 :=
    hP0_le_coeff.trans (by rcases h01 Q.natDegree with h | h <;> linarith)
  have hQ0_le : Q.coeff 0 ≤ 1 :=
    hQ0_le_coeff.trans (by rcases h01 P.natDegree with h | h <;> linarith)
  have hP0_ge : 1 ≤ P.coeff 0 := by
    simpa [hprod, mul_one] using mul_le_mul_of_nonneg_left hQ0_le (hPnonneg 0)
  have hQ0_ge : 1 ≤ Q.coeff 0 := by
    simpa [hprod, one_mul] using mul_le_mul_of_nonneg_right hP0_le (hQnonneg 0)
  exact ⟨le_antisymm hP0_le hP0_ge, le_antisymm hQ0_le hQ0_ge⟩

lemma reverse_eq_self_of_isPalindromic {P : ℝ[X]} (hP0 : P.coeff 0 ≠ 0)
    (hpal : IsPalindromic P) :
    P.reverse = P := by
  have hdeg : P.reverse.natDegree = P.natDegree := by
    rw [Polynomial.reverse_natDegree,
      Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simpa using hP0),
      Nat.sub_zero]
  ext k
  by_cases hk : k ≤ P.natDegree
  · rw [Polynomial.coeff_reverse, Polynomial.revAt_le hk, hpal k hk]
  · have hk' : P.natDegree < k := Nat.lt_of_not_ge hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ hk'),
      Polynomial.coeff_eq_zero_of_natDegree_lt hk']

lemma isPalindromic_right_of_mul_of_left {P Q : ℝ[X]}
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPpal : IsPalindromic P) (hpal : IsPalindromic (P * Q)) :
    IsPalindromic Q := by
  have hP0 : P.coeff 0 = 1 := by
    simpa using (hPpal 0 (Nat.zero_le _)).trans (by simpa using hPmonic.coeff_natDegree)
  have hPQ0 : (P * Q).coeff 0 = 1 := by
    simpa using (hpal 0 (Nat.zero_le _)).trans (by simp [(hPmonic.mul hQmonic).coeff_natDegree])
  have hPrev := reverse_eq_self_of_isPalindromic (by simp [hP0]) hPpal
  have hPQrev := reverse_eq_self_of_isPalindromic (by simp [hPQ0]) hpal
  have hQrev : Q.reverse = Q := mul_left_cancel₀ hPmonic.ne_zero <| by
    calc P * Q.reverse = P.reverse * Q.reverse := by rw [hPrev]
      _ = (P * Q).reverse := (Polynomial.reverse_mul_of_domain P Q).symm
      _ = P * Q := hPQrev
  intro k hk
  rw [show Q.coeff k = Q.reverse.coeff k from by rw [hQrev],
    Polynomial.coeff_reverse, Polynomial.revAt_le hk]

theorem ordered_zero_one_of_palindromic_conv {p q : ℕ → ℝ} {m n : ℕ}
    (hmn : m ≤ n) (hp0 : p 0 = 1) (hpm : p m = 1) (hq0 : q 0 = 1) (hqn : q n = 1)
    (hp_support : ∀ i, m < i → p i = 0) (hq_support : ∀ i, n < i → q i = 0)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hpal : ∀ k, k ≤ m + n → conv p q k = conv p q (m + n - k))
    (h01 : ∀ k, conv p q k = 0 ∨ conv p q k = 1) :
    (∀ i, p i = 0 ∨ p i = 1) ∧ ∀ i, i ≤ m → p i = p (m - i) := by
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨fun i ↦ ?_, fun i hi ↦ by simp [Nat.eq_zero_of_le_zero hi]⟩
    rcases eq_or_ne i 0 with rfl | hi
    · exact Or.inr hp0
    · exact Or.inl (hp_support i (Nat.pos_of_ne_zero hi))
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have hm_lt_n : m < n := Nat.lt_of_le_of_ne hmn fun hEq ↦ by
      have hconvm : conv p q m = (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1))) + 1 + 1 := by
        simpa [hpm, hq0, hp0, show q m = 1 by simpa [hEq] using hqn] using conv_decomp (p := p) (q := q) hm_pos
      have : 0 ≤ ∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1)) :=
        Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (m - (i + 1)))
      rcases h01 m with h0 | h1 <;> linarith
    let S₁ : ℝ := ∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1))
    have hS₁_nonneg : 0 ≤ S₁ :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (m - (i + 1)))
    have hconvm : conv p q m = S₁ + 1 + q m := by
      simpa [S₁, hpm, hq0, hp0, add_comm] using conv_decomp (p := p) (q := q) hm_pos
    have hconvm_eq_one : conv p q m = 1 :=
      (h01 m).resolve_left (by rw [hconvm]; nlinarith [hq_nonneg m])
    have hS₁_zero : S₁ = 0 :=
      ((add_eq_zero_iff_of_nonneg hS₁_nonneg (hq_nonneg m)).1 (by linarith)).1
    have hdiag₁ : ∀ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
        mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (m - (i + 1)))).1 hS₁_zero
    let S₂ : ℝ := ∑ i ∈ Finset.range (m - 1), p (i + 1) * q (n - (i + 1))
    have hS₂_nonneg : 0 ≤ S₂ :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (n - (i + 1)))
    have hconvn : conv p q n = S₂ + q (n - m) + 1 := by
      simpa [S₂, hpm, hqn, hp0, add_left_comm, add_comm] using
        conv_at_degree_right_decomp (p := p) (q := q) hm_pos hm_lt_n hp_support
    have hconvn_eq_one : conv p q n = 1 := by
      linarith [show conv p q m = conv p q n by simpa using hpal m (by omega)]
    have hS₂_zero : S₂ = 0 :=
      ((add_eq_zero_iff_of_nonneg hS₂_nonneg (hq_nonneg (n - m))).1 (by linarith)).1
    have hdiag₂ : ∀ i ∈ Finset.range (m - 1), p (i + 1) * q (n - (i + 1)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
        mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (n - (i + 1)))).1 hS₂_zero
    let Good : ℕ → Prop := fun k ↦
      p k = p (m - k) ∧ q k = q (n - k) ∧ (p k = 0 ∨ p k = 1) ∧ (q k = 0 ∨ q k = 1)
    have hgood : ∀ k, k ≤ m / 2 → Good k := by
      intro k
      refine Nat.strong_induction_on k ?_
      intro k ih hk_half
      by_cases hk0 : k = 0
      · subst hk0
        refine ⟨?_, ?_, Or.inr hp0, Or.inr hq0⟩
        · simpa using hp0.trans hpm.symm
        · simpa using hq0.trans hqn.symm
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have hS_nat :
            ∃ t : ℕ, (t : ℝ) = ∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1)) :=
          exists_natCast_eq_sum_of_zero_one fun i hi ↦ by
            have hi_lt := Finset.mem_range.mp hi
            exact mul_eq_zero_or_one
              (ih (i + 1) (by omega) (by omega)).2.2.1
              (ih (k - (i + 1)) (by omega) (by omega)).2.2.2
        have hconv_low :
            conv p q k = (∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1))) + p k + q k := by
          simpa [hq0, hp0, add_left_comm, add_comm] using conv_decomp (p := p) (q := q) hk_pos
        have hconv_high :
            conv p q (m + n - k) =
              (∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1))) +
                p (m - k) + q (n - k) := by
          simpa [hpm, hqn, add_left_comm, add_comm] using
            conv_high_decomp (p := p) (q := q) hk_pos (by omega) hmn hp_support hq_support
        have hsum_eq : p k + q k = p (m - k) + q (n - k) := by
          have hpalk := hpal k (by omega)
          rw [hconv_low, hconv_high] at hpalk
          have hsum_middle : ∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1)) =
              ∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1)) :=
            Finset.sum_congr rfl fun i hi ↦ by
              have hi_lt := Finset.mem_range.mp hi
              have ⟨hpsym_i, _, _, _⟩ := ih (i + 1) (by omega) (by omega)
              have ⟨_, hqsym_j, _, _⟩ := ih (k - (i + 1)) (by omega) (by omega)
              rw [← hpsym_i, show n - k + (i + 1) = n - (k - (i + 1)) from by omega, ← hqsym_j]
          linarith [hsum_middle ▸ hpalk]
        rcases hS_nat with ⟨t, ht⟩
        have hsum01 : p k + q k = 0 ∨ p k + q k = 1 := by
          have h01k : (p k + q k) + (t : ℝ) = 0 ∨ (p k + q k) + (t : ℝ) = 1 := by
            simpa [hconv_low, ht, add_assoc, add_left_comm, add_comm] using h01 k
          exact eq_zero_or_one_of_nonneg_add_natCast_eq_zero_or_one
            (add_nonneg (hp_nonneg k) (hq_nonneg k)) h01k
        rcases hsum01 with hsum0 | hsum1
        · have ⟨hpk0, hqk0⟩ := (add_eq_zero_iff_of_nonneg (hp_nonneg k) (hq_nonneg k)).1 hsum0
          have ⟨hpmk0, hqnk0⟩ := (add_eq_zero_iff_of_nonneg (hp_nonneg (m - k))
            (hq_nonneg (n - k))).1 (by linarith)
          exact ⟨by simp [hpk0, hpmk0], by simp [hqk0, hqnk0], Or.inl hpk0, Or.inl hqk0⟩
        · have hpk_qnk : p k * q (n - k) = 0 := by
            simpa [show (k - 1) + 1 = k from by omega] using hdiag₂ (k - 1) (Finset.mem_range.mpr (by omega))
          have hpmk_qk : p (m - k) * q k = 0 := by
            simpa [show (m - k - 1) + 1 = m - k from by omega,
              show m - (m - k) = k from by omega] using hdiag₁ (m - k - 1) (Finset.mem_range.mpr (by omega))
          have hprod₁ : p k * (1 - p (m - k)) = 0 := by
            simpa [show q (n - k) = 1 - p (m - k) from by linarith] using hpk_qnk
          have hprod₂ : p (m - k) * (1 - p k) = 0 := by
            simpa [show q k = 1 - p k from by linarith] using hpmk_qk
          have hpsymm : p k = p (m - k) := by nlinarith [hprod₁, hprod₂]
          have hpk_bit : p k = 0 ∨ p k = 1 :=
            (mul_eq_zero.mp (by simpa [hpsymm] using hprod₁)).imp id (fun h ↦ by linarith)
          have hqsymm : q k = q (n - k) := by linarith
          have hq_bit : q k = 0 ∨ q k = 1 := by
            rcases hpk_bit with h | h <;> [right; left] <;> linarith
          exact ⟨hpsymm, hqsymm, hpk_bit, hq_bit⟩
    have hp_symm : ∀ i, i ≤ m → p i = p (m - i) := by
      intro i him
      by_cases hi_half : i ≤ m / 2
      · exact (hgood i hi_half).1
      · simpa [Nat.sub_sub_self him] using ((hgood (m - i) (by omega)).1).symm
    have hp_bit : ∀ i, p i = 0 ∨ p i = 1 := by
      intro i
      by_cases him : m < i
      · exact Or.inl (hp_support i him)
      · by_cases hi_half : i ≤ m / 2
        · exact (hgood i hi_half).2.2.1
        · rw [hp_symm i (by omega)]; exact (hgood (m - i) (by omega)).2.2.1
    exact ⟨hp_bit, hp_symm⟩

/-- Global argument: if `P` is a monic `0`-`1` polynomial with `P.coeff 0 = 1` and
`P * Q` is a `0`-`1` polynomial with `Q` having non-negative coefficients, then
`Q` is a `0`-`1` polynomial. Formalizes the "`Q = R/P ∈ ℤ[x]` + dominance `Q ≤ R`"
argument by lifting `P` and `R` to `ℤ[X]` and using `Polynomial.map_divByMonic`. -/
lemma isZeroOnePoly_factor {P Q : ℝ[X]} (hPmonic : P.Monic)
    (hP01 : IsZeroOnePoly P) (hP0 : P.coeff 0 = 1)
    (hQnn : HasNonnegCoeffs Q) (hR01 : IsZeroOnePoly (P * Q)) :
    IsZeroOnePoly Q := by
  let toZ : ℝ[X] → ℤ[X] := fun f ↦ ∑ k ∈ f.support, (X : ℤ[X]) ^ k
  have toZ_map : ∀ {f : ℝ[X]}, (∀ k, f.coeff k = 0 ∨ f.coeff k = 1) →
      (toZ f).map (Int.castRingHom ℝ) = f := fun {f} h01 ↦ by
    ext n
    simp [toZ, Polynomial.coeff_map, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
    rcases h01 n with hn | hn <;> simp [hn]
  have hP_map := toZ_map hP01
  have hR_map := toZ_map hR01
  have hcast_inj : Function.Injective (Int.castRingHom ℝ) :=
    RingHom.injective_int (Int.castRingHom ℝ)
  have hP_Z_monic : (toZ P).Monic := by
    have hmem : P.natDegree ∈ P.support :=
      Polynomial.mem_support_iff.mpr (hPmonic.coeff_natDegree ▸ one_ne_zero)
    have hdeg : (toZ P).natDegree = P.natDegree := by
      have h := congrArg Polynomial.natDegree hP_map
      rwa [Polynomial.natDegree_map_eq_of_injective hcast_inj] at h
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg]
    simp only [toZ, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single P.natDegree
      (fun j _ hj ↦ if_neg (Ne.symm hj)) (fun h ↦ (h hmem).elim)]
    simp
  have hQ_eq : Q = (P * Q) /ₘ P := (Polynomial.mul_divByMonic_cancel_left _ hPmonic).symm
  have hQ_int : ∀ k, ∃ n : ℤ, (n : ℝ) = Q.coeff k := fun k ↦ by
    refine ⟨((toZ (P * Q)) /ₘ (toZ P)).coeff k, ?_⟩
    have h := Polynomial.map_divByMonic (Int.castRingHom ℝ) hP_Z_monic (p := toZ (P * Q))
    rw [hR_map, hP_map] at h
    calc ((((toZ (P * Q)) /ₘ (toZ P)).coeff k : ℤ) : ℝ)
        = ((toZ (P * Q) /ₘ toZ P).map (Int.castRingHom ℝ)).coeff k := by
          simp [Polynomial.coeff_map]
      _ = (P * Q /ₘ P).coeff k := by rw [h]
      _ = Q.coeff k := by rw [← hQ_eq]
  have hQ_le : ∀ k, Q.coeff k ≤ 1 := fun k ↦ by
    have hdom : Q.coeff k ≤ (P * Q).coeff k := by
      rw [coeff_mul_eq_conv]; unfold conv
      simpa [hP0] using Finset.single_le_sum (s := Finset.range (k + 1)) (a := 0)
        (f := fun i ↦ P.coeff i * Q.coeff (k - i))
        (fun i _ ↦ mul_nonneg (by rcases hP01 i with h | h <;> linarith) (hQnn _))
        (by simp)
    rcases hR01 k with h | h <;> linarith [hQnn k]
  intro k
  obtain ⟨n, hn⟩ := hQ_int k
  have hge : (0 : ℤ) ≤ n := by exact_mod_cast (hn ▸ hQnn k : (0 : ℝ) ≤ (n : ℝ))
  have hle : n ≤ 1 := by exact_mod_cast (hn ▸ hQ_le k : (n : ℝ) ≤ 1)
  interval_cases n <;> [left; right] <;> simpa using hn.symm

lemma factors_zero_one_of_mul_palindromic_ordered {P Q : ℝ[X]}
    (hmn : P.natDegree ≤ Q.natDegree)
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPnonneg : HasNonnegCoeffs P) (hQnonneg : HasNonnegCoeffs Q)
    (hpal : IsPalindromic (P * Q)) (h01 : IsZeroOnePoly (P * Q)) :
    (IsZeroOnePoly P ∧ IsPalindromic P) ∧ (IsZeroOnePoly Q ∧ IsPalindromic Q) := by
  obtain ⟨hP0, hQ0⟩ :=
    constant_coeffs_one_of_palindromic_zero_one_ordered hPmonic hQmonic
      hPnonneg hQnonneg hpal h01
  have hdegPQ : (P * Q).natDegree = P.natDegree + Q.natDegree := hPmonic.natDegree_mul hQmonic
  have hordered :
      IsZeroOnePoly P ∧
        ∀ k, k ≤ P.natDegree → P.coeff k = P.coeff (P.natDegree - k) := by
    simpa [IsZeroOnePoly, HasNonnegCoeffs] using
      ordered_zero_one_of_palindromic_conv (p := P.coeff) (q := Q.coeff) (m := P.natDegree)
        (n := Q.natDegree) hmn hP0 hPmonic.coeff_natDegree hQ0 hQmonic.coeff_natDegree
        (fun i hi ↦ Polynomial.coeff_eq_zero_of_natDegree_lt hi)
        (fun i hi ↦ Polynomial.coeff_eq_zero_of_natDegree_lt hi)
        hPnonneg hQnonneg
        (fun k hk ↦ by
          have hk' : k ≤ (P * Q).natDegree := by simpa [hdegPQ] using hk
          simpa [coeff_mul_eq_conv, hdegPQ, IsPalindromic] using hpal k hk')
        (fun k ↦ by simpa [coeff_mul_eq_conv, IsZeroOnePoly] using h01 k)
  have hPpal : IsPalindromic P := hordered.2
  have hQpal : IsPalindromic Q :=
    isPalindromic_right_of_mul_of_left hPmonic hQmonic hPpal hpal
  have hQ01 : IsZeroOnePoly Q :=
    isZeroOnePoly_factor hPmonic hordered.1 hP0 hQnonneg h01
  exact ⟨⟨hordered.1, hPpal⟩, ⟨hQ01, hQpal⟩⟩

theorem factors_zero_one_of_mul_palindromic {P Q : ℝ[X]}
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPnonneg : HasNonnegCoeffs P) (hQnonneg : HasNonnegCoeffs Q)
    (hpal : IsPalindromic (P * Q)) (h01 : IsZeroOnePoly (P * Q)) :
    (IsZeroOnePoly P ∧ IsPalindromic P) ∧ (IsZeroOnePoly Q ∧ IsPalindromic Q) := by
  by_cases hmn : P.natDegree ≤ Q.natDegree
  · exact factors_zero_one_of_mul_palindromic_ordered hmn hPmonic hQmonic
      hPnonneg hQnonneg hpal h01
  · simpa [and_assoc, and_left_comm, and_comm] using
      factors_zero_one_of_mul_palindromic_ordered (le_of_not_ge hmn) hQmonic hPmonic hQnonneg
        hPnonneg (by simpa [IsPalindromic, mul_comm] using hpal)
        (by simpa [IsZeroOnePoly, mul_comm] using h01)
