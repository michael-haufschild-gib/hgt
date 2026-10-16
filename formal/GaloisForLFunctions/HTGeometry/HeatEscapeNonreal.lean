import GaloisForLFunctions.HTGeometry.HankelHeatEscapePolynomial
import GaloisForLFunctions.HTGeometry.RealRootedCoefficientLimit
import GaloisForLFunctions.HTGeometry.NewtonInequalities
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Nonreal roots in the escaping packet

The first packet containing two roots is `(X + b)^2 + b`, with `b = d-2 > 0`.
Every packet of degree at least two violates Newton's first inequality.
Bounded-degree coefficient convergence transfers this obstruction to nearby
polynomials, without a simple-root or genericity premise.
-/

open Filter Topology Polynomial

namespace HTGeometry
noncomputable section

theorem heatEscapePolynomial_ne_zero (d k : ℕ) : heatEscapePolynomial d k ≠ 0 := by
  intro h
  have hc := heatEscapePolynomial_coeff (d := d) (j := k) le_rfl
  rw [h, coeff_zero, heatEscapeCoeff_self] at hc
  exact zero_ne_one hc

theorem heatEscapePolynomial_natDegree (d k : ℕ) :
    (heatEscapePolynomial d k).natDegree = k := by
  apply le_antisymm
  · exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)
  · apply le_natDegree_of_ne_zero
    rw [heatEscapePolynomial_coeff le_rfl, heatEscapeCoeff_self]
    exact one_ne_zero

theorem heatEscapePolynomial_monic (d k : ℕ) : (heatEscapePolynomial d k).Monic := by
  rw [Monic, leadingCoeff, heatEscapePolynomial_natDegree,
    heatEscapePolynomial_coeff le_rfl, heatEscapeCoeff_self]

/-- The two-root packet is an explicit positive quadratic on the real axis. -/
theorem heatEscapePolynomial_two {d : ℕ} (hd : 2 < d) :
    heatEscapePolynomial d 2 = (X + C ((d - 2 : ℕ) : ℝ)) ^ 2 + C ((d - 2 : ℕ) : ℝ) := by
  have hd1 : d - 1 = (d - 2) + 1 := by omega
  have hexp : ((X + C ((d - 2 : ℕ) : ℝ)) ^ 2 + C ((d - 2 : ℕ) : ℝ) : ℝ[X]) =
      X ^ 2 + C (2 * ((d - 2 : ℕ) : ℝ)) * X +
        C (((d - 2 : ℕ) : ℝ) ^ 2 + ((d - 2 : ℕ) : ℝ)) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  ext i
  by_cases hi : i ≤ 2
  · rw [heatEscapePolynomial_coeff hi]
    rw [hexp]
    interval_cases i <;>
      simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X] <;>
      simp [heatEscapeCoeff, Nat.descFactorial_succ, hd1]
    all_goals ring
  · have hi2 : 2 < i := by omega
    rw [heatEscapePolynomial_coeff_gt hi2]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    have hb : ((X + C ((d - 2 : ℕ) : ℝ)) ^ 2 + C ((d - 2 : ℕ) : ℝ) : ℝ[X]).natDegree ≤ 2 := by
      apply natDegree_add_le_of_degree_le
      · exact natDegree_pow_le.trans (by rw [natDegree_X_add_C])
      · simp
    exact hb.trans_lt hi2

theorem heatEscapePolynomial_two_eval_pos {d : ℕ} (hd : 2 < d) (x : ℝ) :
    0 < (heatEscapePolynomial d 2).eval x := by
  rw [heatEscapePolynomial_two hd]
  simp only [eval_add, eval_pow, eval_X, eval_C]
  have hb : (0 : ℝ) < (d - 2 : ℕ) := by exact_mod_cast (show 0 < d - 2 by omega)
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) hb

theorem heatEscapePolynomial_two_not_splits {d : ℕ} (hd : 2 < d) :
    ¬ (heatEscapePolynomial d 2).Splits := by
  intro hs
  have hdeg : (heatEscapePolynomial d 2).degree ≠ 0 := by
    rw [degree_eq_natDegree (heatEscapePolynomial_ne_zero d 2), heatEscapePolynomial_natDegree]
    norm_num
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hdeg
  exact (ne_of_gt (heatEscapePolynomial_two_eval_pos hd x)) hx

theorem heatEscapePolynomial_newtonCoeff {d k l : ℕ} (hl : l ≤ k) :
    GaloisForLFunctions.SignAlternation.newtonCoeff (heatEscapePolynomial d k) l =
      ((d - 1 - (k - l)).descFactorial l : ℝ) := by
  rw [GaloisForLFunctions.SignAlternation.newtonCoeff, heatEscapePolynomial_natDegree,
    heatEscapePolynomial_coeff (by omega), heatEscapeCoeff, Nat.choose_symm hl,
    Nat.sub_sub_self hl]
  have hc : (k.choose l : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hl))
  exact mul_div_cancel_left₀ _ hc

/-- Every escaping packet with at least two roots contains a nonreal root.
Its first three normalized coefficients are `1,b,b(b+1)`, where `b=d-k>0`. -/
theorem heatEscapePolynomial_not_splits {d k : ℕ} (hkd : k < d) (hk : 2 ≤ k) :
    ¬ (heatEscapePolynomial d k).Splits := by
  intro hs
  have hhyper : GaloisForLFunctions.SignAlternation.Hyperbolic (heatEscapePolynomial d k) :=
    Polynomial.splits_iff_card_roots.mp hs
  have hineq := GaloisForLFunctions.SignAlternation.newton_inequality k
    (heatEscapePolynomial d k) hhyper (heatEscapePolynomial_natDegree d k) 1 le_rfl hk
  have hzero := heatEscapePolynomial_newtonCoeff (d := d) (k := k) (l := 0) (by omega)
  have hone := heatEscapePolynomial_newtonCoeff (d := d) (k := k) (l := 1) (by omega)
  have htwo := heatEscapePolynomial_newtonCoeff (d := d) (k := k) (l := 2) hk
  have hidx1 : d - 1 - (k - 1) = d - k := by omega
  have hidx2 : d - 1 - (k - 2) = d - k + 1 := by omega
  simp only [Nat.sub_self, hzero, hone, htwo, hidx1, hidx2,
    Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.cast_one, Nat.cast_mul, Nat.cast_add, mul_one, one_mul] at hineq
  have hb : (0 : ℝ) < (d - k : ℕ) := by exact_mod_cast (show 0 < d - k by omega)
  nlinarith

/-- A non-real-rooted coefficient limit excludes real-rooted nearby members. -/
theorem eventually_not_splits_of_coeff_limit {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] {p : α → ℝ[X]} {q : ℝ[X]} {N : ℕ}
    (hp : ∀ t, (p t).natDegree ≤ N) (hq : q.natDegree ≤ N) (hq0 : q ≠ 0)
    (hlim : ∀ i, Tendsto (fun t => (p t).coeff i) l (𝓝 (q.coeff i)))
    (hns : ¬ q.Splits) : ∀ᶠ t in l, ¬ (p t).Splits := by
  by_contra h
  have hf : ∃ᶠ t in l, (p t).Splits := by simpa only [not_eventually, not_not] using h
  obtain ⟨u, hu, hs⟩ := exists_seq_forall_of_frequently hf
  exact hns (GaloisForLFunctions.HTGeometry.splits_of_tendsto_coeff
    (fun m => hp (u m)) hq hs (fun i => (hlim i).comp hu) hq0)

/-- Polynomial dilation in bounded-degree coefficient coordinates. -/
def weightedPolynomial (p : ℝ[X]) (N : ℕ) (ε : ℝ) : ℝ[X] :=
  Polynomial.ofFn (N + 1) (fun i : Fin (N + 1) => ε ^ (N - i.val) * p.coeff i)

theorem weightedPolynomial_eq {p : ℝ[X]} {N : ℕ} (hp : p.natDegree ≤ N)
    {ε : ℝ} (hε : ε ≠ 0) :
    weightedPolynomial p N ε = C (ε ^ N) * p.comp (C ε⁻¹ * X) := by
  ext i
  by_cases hi : i ≤ N
  · rw [weightedPolynomial, ofFn_coeff_eq_val_of_lt _ (by omega), coeff_C_mul,
      comp_C_mul_X_coeff, pow_sub₀ ε hε hi, inv_pow]
    ring
  · have hi' : N < i := by omega
    rw [weightedPolynomial, ofFn_coeff_eq_zero_of_ge _ (by omega), coeff_C_mul,
      comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt (hp.trans_lt hi')]
    ring

theorem weightedPolynomial_splits {p : ℝ[X]} {N : ℕ} (hp : p.natDegree ≤ N)
    {ε : ℝ} (hε : ε ≠ 0) (hs : p.Splits) : (weightedPolynomial p N ε).Splits := by
  rw [weightedPolynomial_eq hp hε]
  apply Splits.C_mul
  apply hs.comp_of_natDegree_le_one
  exact (natDegree_mul_le).trans (by simp)

end
end HTGeometry
