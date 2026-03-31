import Mathlib

open Finset Polynomial
open scoped BigOperators

namespace ZeroOnePolyPalindromicCase

/-- A polynomial has all coefficients in {0, 1}. -/
def IsZeroOnePoly (p : ℝ[X]) : Prop :=
  ∀ k : ℕ, p.coeff k = 0 ∨ p.coeff k = 1

/-- A polynomial has all non-negative coefficients. -/
def HasNonnegCoeffs (p : ℝ[X]) : Prop :=
  ∀ k : ℕ, 0 ≤ p.coeff k

/-- A polynomial is palindromic (with respect to its natDegree). -/
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
  refine Finset.induction_on s ?_ ?_ hf
  · intro _
    exact ⟨0, by simp⟩
  · intro a s ha hs hf
    have hf' : ∀ i ∈ s, f i = 0 ∨ f i = 1 := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rcases hs hf' with ⟨t, ht⟩
    rcases hf a (Finset.mem_insert_self a s) with hfa | hfa
    · exact ⟨t, by simp [Finset.sum_insert, ha, hfa, ht]⟩
    · refine ⟨t + 1, ?_⟩
      simp [Finset.sum_insert, ha, hfa, ht, Nat.cast_add, add_comm]

lemma eq_zero_or_one_of_nonneg_add_natCast_eq_zero_or_one {x : ℝ} {t : ℕ}
    (hx : 0 ≤ x) (h : x + (t : ℝ) = 0 ∨ x + (t : ℝ) = 1) :
    x = 0 ∨ x = 1 := by
  rcases h with h | h
  · exact Or.inl <| (add_eq_zero_iff_of_nonneg hx (Nat.cast_nonneg t)).1 h |>.1
  · have ht_le : t ≤ 1 := by
      have ht_real : (t : ℝ) ≤ 1 := by
        linarith
      norm_num at ht_real
      exact ht_real
    interval_cases t
    · right
      exact by simpa using h
    · left
      exact by simpa using h

lemma conv_decomp {p q : ℕ → ℝ} {k : ℕ} (hk : 0 < k) :
    conv p q k =
      (∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1))) + p k * q 0 + p 0 * q k := by
  unfold conv
  have hsplit₁ :
      ∑ i ∈ Finset.range (k + 1), p i * q (k - i) =
        (∑ i ∈ Finset.range k, p (i + 1) * q (k - (i + 1))) + p 0 * q k := by
    simpa [Nat.sub_zero] using
      (Finset.sum_range_succ' (f := fun i ↦ p i * q (k - i)) k)
  have hsplit₂ :
      ∑ i ∈ Finset.range k, p (i + 1) * q (k - (i + 1)) =
        ∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1)) + p k * q 0 := by
    let f : ℕ → ℝ := fun i ↦ p (i + 1) * q (k - (i + 1))
    have hk' : (k - 1) + 1 = k := by omega
    calc
      ∑ i ∈ Finset.range k, f i
        = ∑ i ∈ Finset.range ((k - 1) + 1), f i := by
            rw [hk']
      _ = ∑ i ∈ Finset.range (k - 1), f i + f (k - 1) := by
              rw [Finset.sum_range_succ]
      _ = ∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1)) + p k * q 0 := by
              have hks : (k - 1) + 1 = k := by omega
              simp [f, hks]
  calc
    ∑ i ∈ Finset.range (k + 1), p i * q (k - i)
      = (∑ i ∈ Finset.range k, p (i + 1) * q (k - (i + 1))) + p 0 * q k := hsplit₁
  _ = (∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1))) + p k * q 0 + p 0 * q k := by
      rw [hsplit₂]

lemma conv_eq_right_of_left_degree_zero {p q : ℕ → ℝ}
    (hp0 : p 0 = 1) (hp_support : ∀ i, 0 < i → p i = 0) (k : ℕ) :
    conv p q k = q k := by
  rw [conv, Finset.sum_range_succ']
  have hzero :
      (∑ i ∈ Finset.range k, p (i + 1) * q (k - (i + 1))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [hp_support (i + 1) (Nat.succ_pos _), zero_mul]
  simp [hzero, hp0]

lemma conv_at_degree_right_decomp {p q : ℕ → ℝ} {m n : ℕ}
    (hm0 : 0 < m) (hmn : m < n) (hp_support : ∀ i, m < i → p i = 0) :
    conv p q n =
      (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (n - (i + 1))) + p m * q (n - m) + p 0 * q n := by
  unfold conv
  have hsplit :
      ∑ i ∈ Finset.range (n + 1), p i * q (n - i) =
        ∑ i ∈ Finset.range (m + 1), p i * q (n - i) +
          ∑ i ∈ Finset.range (n - m), p (m + 1 + i) * q (n - (m + 1 + i)) := by
    simpa [show n + 1 = (m + 1) + (n - m) by omega, add_assoc, add_left_comm, add_comm] using
      (Finset.sum_range_add (f := fun i ↦ p i * q (n - i)) (m + 1) (n - m))
  rw [hsplit]
  have htail :
      (∑ i ∈ Finset.range (n - m), p (m + 1 + i) * q (n - (m + 1 + i))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    have hpz : p (m + 1 + i) = 0 := by
      apply hp_support
      omega
    rw [hpz, zero_mul]
  rw [htail, add_zero]
  calc
    ∑ i ∈ Finset.range (m + 1), p i * q (n - i)
      = (∑ i ∈ Finset.range m, p (i + 1) * q (n - (i + 1))) + p 0 * q n := by
          simpa [Nat.sub_zero] using (Finset.sum_range_succ' (f := fun i ↦ p i * q (n - i)) m)
    _ = (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (n - (i + 1))) +
          p m * q (n - m) + p 0 * q n := by
          have hm' : m = (m - 1) + 1 := by omega
          have hnm : n - ((m - 1) + 1) = n - m := by omega
          rw [hm', Finset.sum_range_succ]
          rw [hnm]
          have hms : (m - 1) + 1 = m := by omega
          rw [hms]

lemma conv_high {p q : ℕ → ℝ} {m n k : ℕ}
    (hk : k ≤ m) (hmn : m ≤ n)
    (hp_support : ∀ i, m < i → p i = 0) (hq_support : ∀ i, n < i → q i = 0) :
    conv p q (m + n - k) = ∑ i ∈ Finset.range (k + 1), p (m - k + i) * q (n - i) := by
  unfold conv
  have hsplit₁ :
      ∑ i ∈ Finset.range (m + n - k + 1), p i * q (m + n - k - i) =
        ∑ i ∈ Finset.range (m - k), p i * q (m + n - k - i) +
          ∑ i ∈ Finset.range (n + 1), p (m - k + i) * q (n - i) := by
    have hindex : ∀ i, m + n - k - (m - k + i) = n - i := by
      intro i
      omega
    calc
      ∑ i ∈ Finset.range (m + n - k + 1), p i * q (m + n - k - i)
        = ∑ i ∈ Finset.range (m - k), p i * q (m + n - k - i) +
            ∑ i ∈ Finset.range (n + 1), p (m - k + i) * q (m + n - k - (m - k + i)) := by
              simpa [show m + n - k + 1 = (m - k) + (n + 1) by omega] using
                (Finset.sum_range_add (f := fun i ↦ p i * q (m + n - k - i)) (m - k) (n + 1))
      _ = ∑ i ∈ Finset.range (m - k), p i * q (m + n - k - i) +
            ∑ i ∈ Finset.range (n + 1), p (m - k + i) * q (n - i) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [hindex i]
  rw [hsplit₁]
  have hhead :
      (∑ i ∈ Finset.range (m - k), p i * q (m + n - k - i)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_lt : i < m - k := Finset.mem_range.mp hi
    have hqz : q (m + n - k - i) = 0 := by
      apply hq_support
      omega
    rw [hqz, mul_zero]
  rw [hhead, zero_add]
  have hsplit₂ :
      ∑ i ∈ Finset.range (n + 1), p (m - k + i) * q (n - i) =
        ∑ i ∈ Finset.range (k + 1), p (m - k + i) * q (n - i) +
          ∑ i ∈ Finset.range (n - k), p (m - k + (k + 1 + i)) * q (n - (k + 1 + i)) := by
    simpa [show n + 1 = (k + 1) + (n - k) by omega] using
      (Finset.sum_range_add (f := fun i ↦ p (m - k + i) * q (n - i)) (k + 1) (n - k))
  rw [hsplit₂]
  have htail :
      (∑ i ∈ Finset.range (n - k), p (m - k + (k + 1 + i)) * q (n - (k + 1 + i))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    have hpz : p (m - k + (k + 1 + i)) = 0 := by
      apply hp_support
      omega
    rw [hpz, zero_mul]
  rw [htail, add_zero]

lemma conv_high_decomp {p q : ℕ → ℝ} {m n k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ m) (hmn : m ≤ n)
    (hp_support : ∀ i, m < i → p i = 0) (hq_support : ∀ i, n < i → q i = 0) :
    conv p q (m + n - k) =
      (∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1))) +
        p m * q (n - k) + p (m - k) * q n := by
  rw [conv_high hk hmn hp_support hq_support]
  have hsplit₁ :
      ∑ i ∈ Finset.range (k + 1), p (m - k + i) * q (n - i) =
        (∑ i ∈ Finset.range k, p (m - k + (i + 1)) * q (n - (i + 1))) + p (m - k) * q n := by
    simpa [Nat.sub_zero] using
      (Finset.sum_range_succ' (f := fun i ↦ p (m - k + i) * q (n - i)) k)
  have hsplit₂ :
      ∑ i ∈ Finset.range k, p (m - k + (i + 1)) * q (n - (i + 1)) =
        ∑ i ∈ Finset.range (k - 1), p (m - k + (i + 1)) * q (n - (i + 1)) +
          p (m - k + ((k - 1) + 1)) * q (n - ((k - 1) + 1)) := by
    let f : ℕ → ℝ := fun i ↦ p (m - k + (i + 1)) * q (n - (i + 1))
    have hk' : (k - 1) + 1 = k := by omega
    calc
      ∑ i ∈ Finset.range k, f i
        = ∑ i ∈ Finset.range ((k - 1) + 1), f i := by
            rw [hk']
      _ = ∑ i ∈ Finset.range (k - 1), f i + f (k - 1) := by
              rw [Finset.sum_range_succ]
  have hmiddle :
      ∑ i ∈ Finset.range (k - 1), p (m - k + (i + 1)) * q (n - (i + 1)) =
        ∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1)) := by
    have hreflect := Finset.sum_range_reflect
      (f := fun i ↦ p (m - (i + 1)) * q (n - k + (i + 1))) (k - 1)
    calc
      ∑ i ∈ Finset.range (k - 1), p (m - k + (i + 1)) * q (n - (i + 1))
        = ∑ i ∈ Finset.range (k - 1),
            p (m - (k - (i + 1))) * q (n - k + (k - (i + 1))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hi_lt : i < k - 1 := Finset.mem_range.mp hi
              congr
              · omega
              · have hkn : k ≤ n := le_trans hk hmn
                omega
      _ = ∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1)) := by
              have hleft :
                  ∑ i ∈ Finset.range (k - 1),
                      p (m - (k - (i + 1))) * q (n - k + (k - (i + 1))) =
                    ∑ i ∈ Finset.range (k - 1),
                      p (m - (k - 1 - 1 - i + 1)) * q (n - k + (k - 1 - 1 - i + 1)) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        have hi_lt : i < k - 1 := Finset.mem_range.mp hi
                        have hki : k - (i + 1) = k - 1 - 1 - i + 1 := by omega
                        rw [hki]
              exact hleft.trans hreflect
  have hmk : m - k + ((k - 1) + 1) = m := by omega
  have hnk : n - ((k - 1) + 1) = n - k := by omega
  calc
    ∑ i ∈ Finset.range (k + 1), p (m - k + i) * q (n - i)
      = (∑ i ∈ Finset.range k, p (m - k + (i + 1)) * q (n - (i + 1))) + p (m - k) * q n := hsplit₁
    _ = (∑ i ∈ Finset.range (k - 1), p (m - k + (i + 1)) * q (n - (i + 1))) +
          p (m - k + ((k - 1) + 1)) * q (n - ((k - 1) + 1)) + p (m - k) * q n := by
          rw [hsplit₂]
    _ = (∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1))) +
          p m * q (n - k) + p (m - k) * q n := by
          rw [hmiddle, hmk, hnk]

lemma constant_coeffs_one_of_palindromic_zero_one_ordered {P Q : ℝ[X]}
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPnonneg : HasNonnegCoeffs P) (hQnonneg : HasNonnegCoeffs Q)
    (hpal : IsPalindromic (P * Q)) (h01 : IsZeroOnePoly (P * Q)) :
    P.coeff 0 = 1 ∧ Q.coeff 0 = 1 := by
  have hdegPQ : (P * Q).natDegree = P.natDegree + Q.natDegree := hPmonic.natDegree_mul hQmonic
  have htop : (P * Q).coeff (P.natDegree + Q.natDegree) = 1 := by
    simpa [hdegPQ] using (hPmonic.mul hQmonic).coeff_natDegree
  have hR0 : (P * Q).coeff 0 = 1 := by
    have hpal0 := hpal 0 (Nat.zero_le _)
    simpa [IsPalindromic, hdegPQ, htop] using hpal0
  have hprod : P.coeff 0 * Q.coeff 0 = 1 := by
    simpa [Polynomial.mul_coeff_zero] using hR0
  by_cases hPdeg0 : P.natDegree = 0
  · have hP_eq_one : P = 1 := (hPmonic.natDegree_eq_zero).mp hPdeg0
    have hP0 : P.coeff 0 = 1 := by
      simp [hP_eq_one]
    have hQ0 : Q.coeff 0 = 1 := by
      rw [hP0, one_mul] at hprod
      exact hprod
    exact ⟨hP0, hQ0⟩
  · have hP0_le_conv : P.coeff 0 ≤ conv P.coeff Q.coeff Q.natDegree := by
      unfold conv
      have hle :=
        Finset.single_le_sum
          (s := Finset.range (Q.natDegree + 1))
          (a := 0)
          (f := fun i ↦ P.coeff i * Q.coeff (Q.natDegree - i))
          (fun i _ ↦ mul_nonneg (hPnonneg i) (hQnonneg (Q.natDegree - i)))
          (by simp)
      simpa [Nat.sub_zero, hQmonic.coeff_natDegree, mul_one] using hle
    have hP0_le_coeff : P.coeff 0 ≤ (P * Q).coeff Q.natDegree := by
      simpa [coeff_mul_eq_conv] using hP0_le_conv
    have hQ0_le_conv : Q.coeff 0 ≤ conv P.coeff Q.coeff P.natDegree := by
      unfold conv
      have hle :=
        Finset.single_le_sum
          (s := Finset.range (P.natDegree + 1))
          (a := P.natDegree)
          (f := fun i ↦ P.coeff i * Q.coeff (P.natDegree - i))
          (fun i _ ↦ mul_nonneg (hPnonneg i) (hQnonneg (P.natDegree - i)))
          (by simp)
      simpa [Nat.sub_self, hPmonic.coeff_natDegree, one_mul] using hle
    have hQ0_le_coeff : Q.coeff 0 ≤ (P * Q).coeff P.natDegree := by
      simpa [coeff_mul_eq_conv] using hQ0_le_conv
    have hcoeffQ_le_one : (P * Q).coeff Q.natDegree ≤ 1 := by
      rcases h01 Q.natDegree with h | h <;> linarith
    have hcoeffP_le_one : (P * Q).coeff P.natDegree ≤ 1 := by
      rcases h01 P.natDegree with h | h <;> linarith
    have hP0_le : P.coeff 0 ≤ 1 := hP0_le_coeff.trans hcoeffQ_le_one
    have hQ0_le : Q.coeff 0 ≤ 1 := hQ0_le_coeff.trans hcoeffP_le_one
    have hP0_ge : 1 ≤ P.coeff 0 := by
      have h := mul_le_mul_of_nonneg_left hQ0_le (hPnonneg 0)
      rw [hprod, mul_one] at h
      simpa using h
    have hQ0_ge : 1 ≤ Q.coeff 0 := by
      have h := mul_le_mul_of_nonneg_right hP0_le (hQnonneg 0)
      rw [hprod, one_mul] at h
      simpa using h
    exact ⟨le_antisymm hP0_le hP0_ge, le_antisymm hQ0_le hQ0_ge⟩

lemma reverse_eq_self_of_isPalindromic {P : ℝ[X]} (hP0 : P.coeff 0 ≠ 0)
    (hpal : IsPalindromic P) :
    P.reverse = P := by
  ext k
  by_cases hk : k ≤ P.natDegree
  · rw [Polynomial.coeff_reverse, Polynomial.revAt_le hk, hpal k hk]
  · have hklt : P.natDegree < k := Nat.lt_of_not_ge hk
    have htrail : P.natTrailingDegree = 0 := by
      apply Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
      simpa using hP0
    have hdeg : P.reverse.natDegree = P.natDegree := by
      rw [Polynomial.reverse_natDegree, htrail, Nat.sub_zero]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · symm
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hklt
    · simpa [hdeg] using hklt

lemma isPalindromic_of_reverse_eq_self {P : ℝ[X]} (hrev : P.reverse = P) :
    IsPalindromic P := by
  intro k hk
  calc
    P.coeff k = P.reverse.coeff k := by rw [hrev]
    _ = P.coeff (Polynomial.revAt P.natDegree k) := by rw [Polynomial.coeff_reverse]
    _ = P.coeff (P.natDegree - k) := by rw [Polynomial.revAt_le hk]

lemma isPalindromic_right_of_mul_of_left {P Q : ℝ[X]}
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPpal : IsPalindromic P) (hpal : IsPalindromic (P * Q)) :
    IsPalindromic Q := by
  have hP0 : P.coeff 0 = 1 := by
    calc
      P.coeff 0 = P.coeff (P.natDegree - 0) := hPpal 0 (Nat.zero_le _)
      _ = 1 := by simpa using hPmonic.coeff_natDegree
  have hPQmonic : (P * Q).Monic := hPmonic.mul hQmonic
  have hPQ0 : (P * Q).coeff 0 = 1 := by
    calc
      (P * Q).coeff 0 = (P * Q).coeff ((P * Q).natDegree - 0) := hpal 0 (Nat.zero_le _)
      _ = 1 := by simp [hPQmonic.coeff_natDegree]
  have hPrev : P.reverse = P :=
    reverse_eq_self_of_isPalindromic (by simp [hP0]) hPpal
  have hPQrev : (P * Q).reverse = P * Q :=
    reverse_eq_self_of_isPalindromic (by simp [hPQ0]) hpal
  have hmul : P * Q.reverse = P * Q := by
    calc
      P * Q.reverse = P.reverse * Q.reverse := by rw [hPrev]
      _ = (P * Q).reverse := by
        symm
        exact Polynomial.reverse_mul_of_domain P Q
      _ = P * Q := hPQrev
  have hQrev : Q.reverse = Q := mul_left_cancel₀ hPmonic.ne_zero hmul
  exact isPalindromic_of_reverse_eq_self hQrev

theorem ordered_zero_one_of_palindromic_conv {p q : ℕ → ℝ} {m n : ℕ}
    (hmn : m ≤ n) (hp0 : p 0 = 1) (hpm : p m = 1) (hq0 : q 0 = 1) (hqn : q n = 1)
    (hp_support : ∀ i, m < i → p i = 0) (hq_support : ∀ i, n < i → q i = 0)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hpal : ∀ k, k ≤ m + n → conv p q k = conv p q (m + n - k))
    (h01 : ∀ k, conv p q k = 0 ∨ conv p q k = 1) :
    (∀ i, p i = 0 ∨ p i = 1) ∧ (∀ i, q i = 0 ∨ q i = 1) ∧
      ∀ i, i ≤ m → p i = p (m - i) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hp_degree_zero : ∀ i, 0 < i → p i = 0 := by
      intro i hi
      exact hp_support i hi
    have hp_bit : ∀ i, p i = 0 ∨ p i = 1 := by
      intro i
      by_cases hi : i = 0
      · right
        simpa [hi] using hp0
      · left
        exact hp_degree_zero i (Nat.pos_of_ne_zero hi)
    have hq_bit : ∀ i, q i = 0 ∨ q i = 1 := by
      intro i
      by_cases hi : n < i
      · left
        exact hq_support i hi
      · have hconv : conv p q i = q i := conv_eq_right_of_left_degree_zero hp0 hp_degree_zero i
        simpa [hconv] using h01 i
    have hp_symm : ∀ i, i ≤ 0 → p i = p (0 - i) := by
      intro i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      simp [hi0]
    exact ⟨hp_bit, ⟨hq_bit, hp_symm⟩⟩
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have hm_lt_n : m < n := by
      by_contra hmn'
      have hnm : n ≤ m := le_of_not_gt hmn'
      have hEq : m = n := le_antisymm hmn hnm
      have hsum_nonneg :
          0 ≤ ∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1)) := by
        exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (m - (i + 1)))
      have hconvm : conv p q m = (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1))) + 2 := by
        have hqm : q m = 1 := by simpa [hEq] using hqn
        calc
          conv p q m =
              (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1))) + p m * q 0 + p 0 * q m := by
                simpa using conv_decomp (p := p) (q := q) hm_pos
          _ = (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1))) + 2 := by
                rw [hpm, hq0, hp0, hqm]
                ring
      rcases h01 m with h0 | h1
      · linarith
      · linarith
    let S₁ : ℝ := ∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1))
    have hS₁_nonneg : 0 ≤ S₁ := by
      unfold S₁
      exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (m - (i + 1)))
    have hconvm : conv p q m = S₁ + 1 + q m := by
      unfold S₁
      calc
        conv p q m =
            (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1))) + p m * q 0 + p 0 * q m := by
              simpa using conv_decomp (p := p) (q := q) hm_pos
        _ = S₁ + 1 + q m := by
              simp [S₁, hpm, hq0, hp0, add_comm]
    have hconvm_eq_one : conv p q m = 1 := by
      have hge : (1 : ℝ) ≤ conv p q m := by
        rw [hconvm]
        nlinarith [hS₁_nonneg, hq_nonneg m]
      rcases h01 m with h0 | h1
      · linarith
      · exact h1
    have hS₁_qm_zero : S₁ + q m = 0 := by
      rw [hconvm] at hconvm_eq_one
      linarith
    have hS₁_zero : S₁ = 0 := (add_eq_zero_iff_of_nonneg hS₁_nonneg (hq_nonneg m)).1 hS₁_qm_zero |>.1
    have hdiag₁ :
        ∀ i ∈ Finset.range (m - 1), p (i + 1) * q (m - (i + 1)) = 0 := by
      have hterm_nonneg :
          ∀ i ∈ Finset.range (m - 1), 0 ≤ p (i + 1) * q (m - (i + 1)) := by
        intro i _
        exact mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (m - (i + 1)))
      exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hS₁_zero
    let S₂ : ℝ := ∑ i ∈ Finset.range (m - 1), p (i + 1) * q (n - (i + 1))
    have hS₂_nonneg : 0 ≤ S₂ := by
      unfold S₂
      exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (n - (i + 1)))
    have hconvn : conv p q n = S₂ + q (n - m) + 1 := by
      unfold S₂
      calc
        conv p q n =
            (∑ i ∈ Finset.range (m - 1), p (i + 1) * q (n - (i + 1))) + p m * q (n - m) + p 0 * q n := by
              simpa using conv_at_degree_right_decomp (p := p) (q := q) hm_pos hm_lt_n hp_support
        _ = S₂ + q (n - m) + 1 := by
              simp [S₂, hpm, hqn, hp0, add_left_comm, add_comm]
    have hconvn_eq_one : conv p q n = 1 := by
      have hpalm := hpal m (by omega)
      have hpalm' : conv p q m = conv p q n := by
        simpa using hpalm
      linarith
    have hS₂_qnm_zero : S₂ + q (n - m) = 0 := by
      rw [hconvn] at hconvn_eq_one
      linarith
    have hS₂_zero : S₂ = 0 := (add_eq_zero_iff_of_nonneg hS₂_nonneg (hq_nonneg (n - m))).1 hS₂_qnm_zero |>.1
    have hdiag₂ :
        ∀ i ∈ Finset.range (m - 1), p (i + 1) * q (n - (i + 1)) = 0 := by
      have hterm_nonneg :
          ∀ i ∈ Finset.range (m - 1), 0 ≤ p (i + 1) * q (n - (i + 1)) := by
        intro i _
        exact mul_nonneg (hp_nonneg (i + 1)) (hq_nonneg (n - (i + 1)))
      exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hS₂_zero
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
            ∃ t : ℕ, (t : ℝ) = ∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1)) := by
          apply exists_natCast_eq_sum_of_zero_one
          intro i hi
          have hi_lt : i < k - 1 := Finset.mem_range.mp hi
          have hi1_lt : i + 1 < k := by omega
          have hkmi_lt : k - (i + 1) < k := by omega
          rcases ih (i + 1) hi1_lt (le_trans (Nat.le_of_lt hi1_lt) hk_half) with
            ⟨_, _, hpbit, _⟩
          rcases ih (k - (i + 1)) hkmi_lt (le_trans (Nat.le_of_lt hkmi_lt) hk_half) with
            ⟨_, _, _, hqbit⟩
          exact mul_eq_zero_or_one hpbit hqbit
        have hconv_low :
            conv p q k = (∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1))) + p k + q k := by
          calc
            conv p q k =
                (∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1))) + p k * q 0 + p 0 * q k := by
                  simpa using conv_decomp (p := p) (q := q) hk_pos
            _ = (∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1))) + p k + q k := by
                  simp [hq0, hp0, add_left_comm, add_comm]
        have hconv_high :
            conv p q (m + n - k) =
              (∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1))) +
                p (m - k) + q (n - k) := by
          calc
            conv p q (m + n - k) =
                (∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1))) +
                  p m * q (n - k) + p (m - k) * q n := by
                    simpa using conv_high_decomp (p := p) (q := q) hk_pos (by omega) hmn hp_support hq_support
            _ = (∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1))) +
                  p (m - k) + q (n - k) := by
                    simp [hpm, hqn, add_left_comm, add_comm]
        have hsum_eq :
            p k + q k = p (m - k) + q (n - k) := by
          have hpalk := hpal k (by omega)
          rw [hconv_low, hconv_high] at hpalk
          have hsum_middle :
              ∑ i ∈ Finset.range (k - 1), p (m - (i + 1)) * q (n - k + (i + 1)) =
                ∑ i ∈ Finset.range (k - 1), p (i + 1) * q (k - (i + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < k - 1 := Finset.mem_range.mp hi
            have hi1_lt : i + 1 < k := by omega
            have hkmi_lt : k - (i + 1) < k := by omega
            rcases ih (i + 1) hi1_lt (le_trans (Nat.le_of_lt hi1_lt) hk_half) with
              ⟨hpsym_i, _, _, _⟩
            rcases ih (k - (i + 1)) hkmi_lt (le_trans (Nat.le_of_lt hkmi_lt) hk_half) with
              ⟨_, hqsym_j, _, _⟩
            have hnk : n - (k - (i + 1)) = n - k + (i + 1) := by
              have hk_le_n : k ≤ n := le_trans (by omega) hmn
              omega
            calc
              p (m - (i + 1)) * q (n - k + (i + 1))
                = p (i + 1) * q (n - k + (i + 1)) := by rw [← hpsym_i]
              _ = p (i + 1) * q (n - (k - (i + 1))) := by rw [hnk]
              _ = p (i + 1) * q (k - (i + 1)) := by rw [← hqsym_j]
          rw [hsum_middle] at hpalk
          linarith
        rcases hS_nat with ⟨t, ht⟩
        have hsum01 : p k + q k = 0 ∨ p k + q k = 1 := by
          have h01k : (p k + q k) + (t : ℝ) = 0 ∨ (p k + q k) + (t : ℝ) = 1 := by
            simpa [hconv_low, ht, add_assoc, add_left_comm, add_comm] using h01 k
          exact eq_zero_or_one_of_nonneg_add_natCast_eq_zero_or_one
            (add_nonneg (hp_nonneg k) (hq_nonneg k)) h01k
        rcases hsum01 with hsum0 | hsum1
        · have hpkqk : p k = 0 ∧ q k = 0 :=
            (add_eq_zero_iff_of_nonneg (hp_nonneg k) (hq_nonneg k)).1 hsum0
          have hhigh0 : p (m - k) + q (n - k) = 0 := by
            linarith
          have hpmqnk : p (m - k) = 0 ∧ q (n - k) = 0 :=
            (add_eq_zero_iff_of_nonneg (hp_nonneg (m - k)) (hq_nonneg (n - k))).1 hhigh0
          refine ⟨?_, ?_, Or.inl hpkqk.1, Or.inl hpkqk.2⟩
          · simp [hpkqk.1, hpmqnk.1]
          · simp [hpkqk.2, hpmqnk.2]
        · have hk_range : k - 1 ∈ Finset.range (m - 1) := by
            exact Finset.mem_range.mpr (by omega)
          have hmk_range : m - k - 1 ∈ Finset.range (m - 1) := by
            exact Finset.mem_range.mpr (by omega)
          have hpk_qnk : p k * q (n - k) = 0 := by
            have hdiag := hdiag₂ (k - 1) hk_range
            have hk1 : (k - 1) + 1 = k := by omega
            rw [hk1] at hdiag
            exact hdiag
          have hpmk_qk : p (m - k) * q k = 0 := by
            have hdiag := hdiag₁ (m - k - 1) hmk_range
            have hm1 : (m - k - 1) + 1 = m - k := by omega
            have hm2 : m - (m - k) = k := by omega
            rw [hm1, hm2] at hdiag
            exact hdiag
          have hqk_eq : q k = 1 - p k := by
            linarith
          have hqnk_eq : q (n - k) = 1 - p (m - k) := by
            linarith
          have hprod₁ : p k * (1 - p (m - k)) = 0 := by
            simpa [hqnk_eq] using hpk_qnk
          have hprod₂ : p (m - k) * (1 - p k) = 0 := by
            simpa [hqk_eq] using hpmk_qk
          have hpsymm : p k = p (m - k) := by
            nlinarith [hprod₁, hprod₂]
          have hpk_bit : p k = 0 ∨ p k = 1 := by
            have hprod : p k * (1 - p k) = 0 := by
              simpa [hpsymm] using hprod₁
            rcases mul_eq_zero.mp hprod with hpk0 | hpk1
            · exact Or.inl hpk0
            · right
              linarith
          have hqsymm : q k = q (n - k) := by
            linarith
          have hq_bit : q k = 0 ∨ q k = 1 := by
            rcases hpk_bit with hpk0 | hpk1
            · right
              linarith
            · left
              linarith
          exact ⟨hpsymm, hqsymm, hpk_bit, hq_bit⟩
    have hp_symm : ∀ i, i ≤ m → p i = p (m - i) := by
      intro i him
      by_cases hi_half : i ≤ m / 2
      · exact (hgood i hi_half).1
      · have hmir_half : m - i ≤ m / 2 := by
          omega
        have hmir : p (m - i) = p (m - (m - i)) := (hgood (m - i) hmir_half).1
        have hmii : m - (m - i) = i := by
          omega
        simpa [hmii] using hmir.symm
    have hp_bit : ∀ i, p i = 0 ∨ p i = 1 := by
      intro i
      by_cases him : m < i
      · left
        exact hp_support i him
      · by_cases hi_half : i ≤ m / 2
        · rcases hgood i hi_half with ⟨_, _, hpbit, _⟩
          exact hpbit
        · have hmir_half : m - i ≤ m / 2 := by
            omega
          rcases hgood (m - i) hmir_half with ⟨hpsymm, _, hpbit, _⟩
          have hmii : m - (m - i) = i := by
            omega
          have hEq : p (m - i) = p i := by
            simpa [hmii] using hpsymm
          rcases hpbit with hpi0 | hpi1
          · left
            rw [hEq] at hpi0
            exact hpi0
          · right
            rw [hEq] at hpi1
            exact hpi1
    have hq_bit : ∀ i, q i = 0 ∨ q i = 1 := by
      intro i
      refine Nat.strong_induction_on i ?_
      intro i ih
      by_cases hi_n : n < i
      · left
        exact hq_support i hi_n
      · by_cases hi0 : i = 0
        · right
          simpa [hi0] using hq0
        · have hN_nat :
              ∃ t : ℕ, (t : ℝ) = ∑ a ∈ Finset.range i, p (a + 1) * q (i - (a + 1)) := by
            apply exists_natCast_eq_sum_of_zero_one
            intro a ha
            have ha_lt : a < i := Finset.mem_range.mp ha
            have hprev : i - (a + 1) < i := by
              omega
            exact mul_eq_zero_or_one (hp_bit (a + 1)) (ih (i - (a + 1)) hprev)
          rcases hN_nat with ⟨t, ht⟩
          have hconv_i :
              conv p q i = (∑ a ∈ Finset.range i, p (a + 1) * q (i - (a + 1))) + q i := by
            rw [conv, Finset.sum_range_succ']
            simp [hp0, add_comm]
          have h01i : q i + (t : ℝ) = 0 ∨ q i + (t : ℝ) = 1 := by
            simpa [hconv_i, ht, add_assoc, add_left_comm, add_comm] using h01 i
          exact eq_zero_or_one_of_nonneg_add_natCast_eq_zero_or_one (hq_nonneg i) h01i
    exact ⟨hp_bit, ⟨hq_bit, hp_symm⟩⟩

theorem factors_zero_one_of_mul_palindromic {P Q : ℝ[X]}
    (hPmonic : P.Monic) (hQmonic : Q.Monic)
    (hPnonneg : HasNonnegCoeffs P) (hQnonneg : HasNonnegCoeffs Q)
    (hpal : IsPalindromic (P * Q)) (h01 : IsZeroOnePoly (P * Q)) :
    (IsZeroOnePoly P ∧ IsPalindromic P) ∧ (IsZeroOnePoly Q ∧ IsPalindromic Q) := by
  have hdegPQ : (P * Q).natDegree = P.natDegree + Q.natDegree := hPmonic.natDegree_mul hQmonic
  by_cases hmn : P.natDegree ≤ Q.natDegree
  · obtain ⟨hP0, hQ0⟩ :=
      constant_coeffs_one_of_palindromic_zero_one_ordered hPmonic hQmonic
        hPnonneg hQnonneg hpal h01
    have hordered :
        IsZeroOnePoly P ∧ IsZeroOnePoly Q ∧
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
    have hPpal : IsPalindromic P := hordered.2.2
    have hQpal : IsPalindromic Q :=
      isPalindromic_right_of_mul_of_left hPmonic hQmonic hPpal hpal
    exact ⟨⟨hordered.1, hPpal⟩, ⟨hordered.2.1, hQpal⟩⟩
  · have hnm : Q.natDegree ≤ P.natDegree := le_of_not_ge hmn
    have hpal' : IsPalindromic (Q * P) := by
      simpa [IsPalindromic, mul_comm] using hpal
    have h01' : IsZeroOnePoly (Q * P) := by
      simpa [IsZeroOnePoly, mul_comm] using h01
    obtain ⟨hQ0, hP0⟩ :=
      constant_coeffs_one_of_palindromic_zero_one_ordered hQmonic hPmonic
        hQnonneg hPnonneg hpal' h01'
    have hdegQP : (Q * P).natDegree = Q.natDegree + P.natDegree := hQmonic.natDegree_mul hPmonic
    have hswap :
        IsZeroOnePoly Q ∧ IsZeroOnePoly P ∧
          ∀ k, k ≤ Q.natDegree → Q.coeff k = Q.coeff (Q.natDegree - k) := by
      simpa [IsZeroOnePoly, HasNonnegCoeffs] using
        ordered_zero_one_of_palindromic_conv (p := Q.coeff) (q := P.coeff)
          (m := Q.natDegree) (n := P.natDegree) hnm hQ0 hQmonic.coeff_natDegree
          hP0 hPmonic.coeff_natDegree
          (fun i hi ↦ Polynomial.coeff_eq_zero_of_natDegree_lt hi)
          (fun i hi ↦ Polynomial.coeff_eq_zero_of_natDegree_lt hi)
          hQnonneg hPnonneg
          (fun k hk ↦ by
            have hk' : k ≤ (Q * P).natDegree := by simpa [hdegQP] using hk
            have hk'' : k ≤ (P * Q).natDegree := by simpa [mul_comm] using hk'
            have hpal' : (Q * P).coeff k = (Q * P).coeff ((Q * P).natDegree - k) := by
              simpa [mul_comm] using hpal k hk''
            simpa [coeff_mul_eq_conv, hdegQP] using hpal')
          (fun k ↦ by
            have h01' : (Q * P).coeff k = 0 ∨ (Q * P).coeff k = 1 := by
              simpa [mul_comm] using h01 k
            simpa [coeff_mul_eq_conv] using h01')
    have hQpal : IsPalindromic Q := hswap.2.2
    have hPpal : IsPalindromic P :=
      isPalindromic_right_of_mul_of_left hQmonic hPmonic hQpal hpal'
    exact ⟨⟨hswap.2.1, hPpal⟩, ⟨hswap.1, hQpal⟩⟩