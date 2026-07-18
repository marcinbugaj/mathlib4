/-
Copyright (c) 2026 Marcin Bugaj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcin Bugaj
-/
import Mathlib.Analysis.Convex.Majorization
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.MeanInequalities

/-!
# Muirhead's inequality

If the exponent tuple `a` is majorized by `b` (`a ≺ b`), then the symmetric Muirhead sum
`evalMuirheadSum vars a = ∑_σ ∏_i vars (σ i) ^ a i` is monotone:
`evalMuirheadSum vars a ≤ evalMuirheadSum vars b`, provided every variable is nonzero. The proof
decomposes `a ≺ b` into a finite chain of T-transforms (see `Mathlib.Analysis.Convex.Majorization`)
and applies the two-variable weighted AM–GM inequality at each step.

## Main definitions

* `evalMonomial σ vars exponents`: the monomial `∏_i vars (σ i) ^ exponents i`.
* `evalMuirheadSum vars exponents`: the sum of `evalMonomial` over all permutations `σ`.

## Main statements

* `muirhead`: `a ≺ b → evalMuirheadSum vars a ≤ evalMuirheadSum vars b`, for nonvanishing `vars`.

## References

* [Hardy–Littlewood–Pólya, *Inequalities*, Theorem 45][hardyLittlewoodPolya1952]

## Tags

Muirhead inequality, majorization, symmetric mean, AM-GM
-/

namespace Muirhead

open NNReal Majorization

/-! ### The Muirhead symmetric sum -/

/-- The monomial `∏_i vars (σ i) ^ exponents i`, with the variables permuted by `σ`. -/
noncomputable def evalMonomial {n} (σ : Equiv.Perm (Fin n))
    (vars : Fin n → ℝ≥0) (exponents : Fin n → ℝ) : ℝ≥0 :=
  ∏ i : Fin n, vars (σ i) ^ exponents i

/-- The Muirhead symmetric sum `∑_σ ∏_i vars (σ i) ^ exponents i` over all permutations `σ`. -/
noncomputable def evalMuirheadSum {n} (vars : Fin n → ℝ≥0) (exponents : Fin n → ℝ) : ℝ≥0 :=
  ∑ σ : Equiv.Perm (Fin n), evalMonomial σ vars exponents

/-! ### Two-point weighted AM–GM -/

private lemma sum_of_monomials_swap {n vars k l a} {σ : Equiv.Perm (Fin n)} (lnk : l ≠ k) :
    evalMonomial σ vars a + evalMonomial (σ * Equiv.swap k l) vars a
  = (∏ i : Fin n with i ≠ k ∧ i ≠ l, vars (σ i) ^ a i)
  * (vars (σ k) ^ a k * vars (σ l) ^ a l + vars (σ k) ^ a l * vars (σ l) ^ a k) := by
  unfold evalMonomial
  have hfix : ∀ i ∈ Finset.univ.filter (fun x ↦ x ≠ k ∧ x ≠ l),
         vars ((σ * Equiv.swap k l) i) ^ a i = vars (σ i) ^ a i := by
    intro i inkl
    rw [Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne
          (Finset.mem_filter.mp inkl).2.1
          (Finset.mem_filter.mp inkl).2.2]
  rw [prod_split_two lnk fun i ↦ vars (σ i) ^ a i,
      prod_split_two lnk fun i ↦ vars ((σ * Equiv.swap k l) i) ^ a i,
      Finset.prod_congr rfl hfix]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- Two-point Muirhead / weighted AM–GM step: if `(m, n)` is majorized by `(k, l)`
(same sum, `|k - l| ≥ |m - n|`), then `aᵐbⁿ + aⁿbᵐ ≤ aᵏbˡ + aˡbᵏ`.
Requires `a ≠ 0`, `b ≠ 0` (otherwise false for negative exponents, e.g.
`a = 0, b = 1, k = -1, l = 1, m = n = 0` gives `0 ≥ 2`). -/
lemma exp_inequality {k l m n : ℝ} {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (klmn : k + l = m + n) (diff : |k - l| ≥ |m - n|) :
    a ^ k * b ^ l + a ^ l * b ^ k ≥ a ^ m * b ^ n + a ^ n * b ^ m := by
  -- Step 1: write `(m, n)` as a convex combination `m = (1-t)k + tl`, `n = tk + (1-t)l`.
  obtain ⟨t, ht0, ht1, hm, hn⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      m = (1 - t) * k + t * l ∧ n = t * k + (1 - t) * l := by
    rcases eq_or_ne l k with hlk | hlk
    · rw [hlk, sub_self, abs_zero] at diff
      have hmn : m = n := by linarith [abs_eq_zero.mp (le_antisymm diff (abs_nonneg (m - n)))]
      exact ⟨0, le_rfl, zero_le_one, by linarith, by linarith⟩
    · have hlk' : l - k ≠ 0 := sub_ne_zero.mpr hlk
      have hprod : (m - k) * (m - l) ≤ 0 := by
        have hn' : n = k + l - m := by linarith
        subst hn'
        nlinarith [sq_abs (m - (k + l - m)), sq_abs (k - l), abs_nonneg (m - (k + l - m)),
          abs_nonneg (k - l), mul_self_le_mul_self (abs_nonneg (m - (k + l - m))) diff]
      refine ⟨(m - k) / (l - k), ?_, ?_, ?_, ?_⟩
      · rcases lt_or_gt_of_ne hlk' with h | h
        · rw [div_nonneg_iff]; right; constructor <;> nlinarith [hprod, h]
        · rw [div_nonneg_iff]; left;  constructor <;> nlinarith [hprod, h]
      · rcases lt_or_gt_of_ne hlk' with h | h
        · rw [div_le_one_iff]; right; right; constructor <;> nlinarith [hprod, h]
        · rw [div_le_one_iff]; left;  constructor <;> nlinarith [hprod, h]
      · field_simp; ring
      · rw [show n = k + l - m from by linarith]; field_simp; ring
  -- Step 2: each mixed term is a weighted geometric mean of `aᵏbˡ` and `aˡbᵏ`.
  have hmn₁ : a ^ m * b ^ n = (a ^ k * b ^ l) ^ (1 - t) * (a ^ l * b ^ k) ^ t := by
    rw [hm, hn, NNReal.mul_rpow, NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul,
        ← NNReal.rpow_mul, ← NNReal.rpow_mul, mul_mul_mul_comm,
        ← NNReal.rpow_add ha, ← NNReal.rpow_add hb]
    congr 1 <;> ring
  have hmn₂ : a ^ n * b ^ m = (a ^ l * b ^ k) ^ (1 - t) * (a ^ k * b ^ l) ^ t := by
    rw [hm, hn, NNReal.mul_rpow, NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul,
        ← NNReal.rpow_mul, ← NNReal.rpow_mul, mul_mul_mul_comm,
        ← NNReal.rpow_add ha, ← NNReal.rpow_add hb]
    congr 1 <;> ring
  rw [ge_iff_le, hmn₁, hmn₂]
  -- Step 3: two-term weighted AM–GM on `A := aᵏbˡ` and `B := aˡbᵏ`.
  set A := a ^ k * b ^ l
  set B := a ^ l * b ^ k
  let w₁ : ℝ≥0 := ⟨1 - t, by linarith⟩
  let w₂ : ℝ≥0 := ⟨t, ht0⟩
  have hw : w₁ + w₂ = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, NNReal.coe_one]; change 1 - t + t = 1; ring
  have e₁ : A ^ (1 - t) * B ^ t ≤ w₁ * A + w₂ * B :=
    NNReal.geom_mean_le_arith_mean2_weighted w₁ w₂ A B hw
  have e₂ : B ^ (1 - t) * A ^ t ≤ w₁ * B + w₂ * A :=
    NNReal.geom_mean_le_arith_mean2_weighted w₁ w₂ B A hw
  calc A ^ (1 - t) * B ^ t + B ^ (1 - t) * A ^ t
      ≤ (w₁ * A + w₂ * B) + (w₁ * B + w₂ * A) := add_le_add e₁ e₂
    _ = (w₁ + w₂) * A + (w₁ + w₂) * B := by ring
    _ = A + B := by rw [hw, one_mul, one_mul]

/-! ### One T-transform does not increase the Muirhead sum -/

/-- Pairing identity: doubling a Muirhead sum groups the permutations into pairs
`{σ, σ * swap k l}`. -/
private lemma two_mul_evalMuirheadSum_eq {n} (vars : Fin n → ℝ≥0) (c : Fin n → ℝ) (k l : Fin n) :
    2 * evalMuirheadSum vars c
      = ∑ σ : Equiv.Perm (Fin n),
          (evalMonomial σ vars c + evalMonomial (σ * Equiv.swap k l) vars c) := by
  unfold evalMuirheadSum
  rw [Finset.sum_add_distrib, two_mul]
  congr 1
  exact (Equiv.sum_comp (Equiv.mulRight (Equiv.swap k l)) (evalMonomial · vars c)).symm

lemma evalMuirheadSum_le_of_tTransform {n b a k l lambda vars}
    (hvars : ∀ i, vars i ≠ 0) (t : TTransform b a k l lambda) :
    @evalMuirheadSum n vars a ≥ @evalMuirheadSum n vars b := by
  have l_ne_k : l ≠ k := fun h ↦ ne_of_gt t.ak_gt_al (congrArg a h).symm
  have htwo_mul := calc 2 * @evalMuirheadSum n vars a
    _ = ∑ σ : Equiv.Perm (Fin n),
          (evalMonomial σ vars a + evalMonomial (σ * Equiv.swap k l) vars a) :=
        two_mul_evalMuirheadSum_eq vars a k l
    _ = ∑ σ : Equiv.Perm (Fin n),
          (∏ i : Fin n with i ≠ k ∧ i ≠ l, vars (σ i) ^ a i) *
            (vars (σ k) ^ a k * vars (σ l) ^ a l + vars (σ k) ^ a l * vars (σ l) ^ a k) := by
        simp only [sum_of_monomials_swap l_ne_k]
    _ ≥ ∑ σ : Equiv.Perm (Fin n),
          (∏ i : Fin n with i ≠ k ∧ i ≠ l, vars (σ i) ^ a i) *
            (vars (σ k) ^ b k * vars (σ l) ^ b l + vars (σ k) ^ b l * vars (σ l) ^ b k) := by
        apply Finset.sum_le_sum
        intro σ _
        apply mul_le_mul_of_nonneg_left
        case ha => exact zero_le
        apply exp_inequality
        case hbc.ha => exact hvars (σ k)
        case hbc.hb => exact hvars (σ l)
        case hbc.klmn => simp [t.bk, t.bl]
        case hbc.diff =>
          have hak_sub_al_pos : a k - a l > 0 := sub_pos.mpr t.ak_gt_al
          have hdiff : a k + (a l - a k) * lambda - (a l - (a l - a k) * lambda)
              = a k - a l - 2 * (a k - a l) * lambda := by ring
          rw [t.bk, t.bl, hdiff, abs_of_pos hak_sub_al_pos, ge_iff_le, abs_le]
          constructor <;> nlinarith [t.lambda_0_1.1, t.lambda_0_1.2, hak_sub_al_pos]
    _ = ∑ σ : Equiv.Perm (Fin n),
          (∏ i : Fin n with i ≠ k ∧ i ≠ l, vars (σ i) ^ b i) *
            (vars (σ k) ^ b k * vars (σ l) ^ b l + vars (σ k) ^ b l * vars (σ l) ^ b k) := by
        refine Finset.sum_congr rfl fun σ _ ↦ ?_
        congr 1
        exact Finset.prod_congr rfl fun i hi ↦ by
          rw [t.other_unchanged i (Finset.mem_filter.mp hi).2]
    _ = ∑ σ : Equiv.Perm (Fin n),
          (evalMonomial σ vars b + evalMonomial (σ * Equiv.swap k l) vars b) :=
        Finset.sum_congr rfl (fun σ _ ↦ (sum_of_monomials_swap l_ne_k).symm)
    _ = 2 * @evalMuirheadSum n vars b := (two_mul_evalMuirheadSum_eq vars b k l).symm
  simp only [ge_iff_le, Nat.ofNat_pos, le_of_mul_le_mul_left htwo_mul]

/-! ### Permutation invariance of the Muirhead sum -/

lemma evalMuirheadSum_comp_perm
  {n} {vars : Fin n → ℝ≥0} {exponents : Fin n → ℝ} (perm : Equiv.Perm (Fin n)) :
  evalMuirheadSum vars exponents = evalMuirheadSum vars (exponents ∘ perm) := by
  -- Permuting the exponents is absorbed by reindexing the sum over all `σ` (the bijection
  -- `σ ↦ σ * perm`), whose summands match after reindexing the inner product.
  unfold evalMuirheadSum
  apply Fintype.sum_equiv (Equiv.mulRight perm)
  intro σ
  unfold evalMonomial
  apply Fintype.prod_equiv perm⁻¹
  intro i
  simp only [Function.comp_apply, Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
    Equiv.apply_symm_apply]

/-! ### Muirhead's inequality -/

/-- **Muirhead's inequality.** If the exponent tuple `a` is majorized by `b` and every variable is
nonzero, then the Muirhead symmetric sum for `a` is at most that for `b`. -/
theorem muirhead {n} {vars : Fin n → ℝ≥0} {a b : Fin n → ℝ} (hvars : ∀ i, vars i ≠ 0) :
  a ≺ b → evalMuirheadSum vars a ≤ evalMuirheadSum vars b := by
  rw [majorizes_iff_reflTransGen_relatedByTTransform]
  rw [evalMuirheadSum_comp_perm (exponents := a) (sortDesc a)]
  rw [evalMuirheadSum_comp_perm (exponents := b) (sortDesc b)]
  intro rel
  suffices H : ∀ x y : Fin n → ℝ, Relation.ReflTransGen RelatedByTTransform x y →
        evalMuirheadSum vars x ≤ evalMuirheadSum vars y by exact H _ _ rel
  intro x y rel
  induction rel with
  | refl => simp only [le_refl]
  | @tail p q _ step ih =>
    obtain ⟨_, _, _, ttransform⟩ := step
    exact ih.trans (evalMuirheadSum_le_of_tTransform hvars ttransform)

end Muirhead
