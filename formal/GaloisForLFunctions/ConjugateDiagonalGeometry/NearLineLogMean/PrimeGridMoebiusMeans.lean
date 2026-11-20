import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimitiveSpectrumOfTheMoebiusGram

/-!
# Binomial sampling of the critical Möbius polynomial

Iterating the symmetric three-point mean multiplies a cosine by
`((1+cos(Lh))/2)^r`. At spacing `2π/log p` the surviving log ratios
are powers of `p`. Coprimality and squarefreeness reduce the off-diagonal
spectrum to the two directions of the single prime ratio `p`.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.MultiscaleMollifiedZetaField

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

noncomputable section

/-- Symmetric binomial height average, with weights one quarter, one half, one quarter. -/
def binomialHeightMean (h : ℝ) : Module.End ℝ (ℝ → ℝ) where
  toFun f t := (f (t-h) + 2*f t + f (t+h))/4
  map_add' f g := by funext t; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext t; dsimp; ring

private def wave (L : ℝ) (t : ℝ) := Real.cos (L*t)
/-- Fourier multiplier of one symmetric binomial height average. -/
def heightMultiplier (L h : ℝ) := (1+Real.cos (L*h))/2

private theorem mean_wave (h L : ℝ) :
    binomialHeightMean h (wave L) = heightMultiplier L h • wave L := by
  funext t
  change (Real.cos (L*(t-h)) + 2*Real.cos (L*t) + Real.cos (L*(t+h)))/4 =
    heightMultiplier L h * Real.cos (L*t)
  rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
  unfold heightMultiplier
  ring

private theorem mean_const (h c : ℝ) : binomialHeightMean h (fun _ => c) = fun _ => c := by
  funext t
  change (c+2*c+c)/4=c
  ring

private theorem mean_power_wave (r : ℕ) (h L : ℝ) :
    (binomialHeightMean h ^ r) (wave L) = heightMultiplier L h^r • wave L := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, mean_wave, smul_smul, pow_succ]

private theorem mean_power_const (r : ℕ) (h c : ℝ) :
    (binomialHeightMean h ^ r) (fun _ => c) = fun _ => c := by
  induction r with
  | zero => rfl
  | succ r ih => rw [pow_succ', Module.End.mul_apply, ih, mean_const]

/-- Exact pointwise spectrum of every finite binomial average. -/
theorem critical_power_binomial (N r : ℕ) (t h : ℝ) :
    (binomialHeightMean h ^ r) (fun x => ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint x)‖^2) t =
      (∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n) +
        ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 * heightMultiplier (Real.log q.1-Real.log q.2) h ^ r *
          Real.cos ((Real.log q.1-Real.log q.2)*t) := by
  let D := ∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n
  have hf : (fun x => ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint x)‖^2) = (fun _ : ℝ => D) +
      ∑ q ∈ primitiveRatioPairs N, atom N q.1 q.2 • wave (Real.log q.1-Real.log q.2) := by
    funext x
    simpa only [D, wave, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      critical_power_spectrum N x
  rw [hf, map_add, map_sum, mean_power_const]
  simp only [map_smul, mean_power_wave, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    wave, mul_assoc] <;> rfl

private theorem keep_limit (L h : ℝ) :
    Tendsto (fun r : ℕ => heightMultiplier L h^r) atTop (𝓝 (if Real.cos (L*h) = 1 then 1 else 0)) := by
  split_ifs with hc
  · simp [heightMultiplier, hc]
  · apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · unfold heightMultiplier; linarith only [Real.neg_one_le_cos (L*h)]
    · unfold heightMultiplier; linarith only [lt_of_le_of_ne (Real.cos_le_one _) hc]

private theorem positive_resonance {p a b j : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hcop : a.Coprime b) (hne : a ≠ b) (hs : Squarefree a)
    (hlog : Real.log a-Real.log b = (j : ℝ)*Real.log p) : a = p ∧ b = 1 := by
  have he : a = b*p^j := by
    have H : (a : ℝ) = (b : ℝ)*(p : ℝ)^j := by
      calc (a : ℝ) = Real.exp (Real.log a) := (Real.exp_log (Nat.cast_pos.mpr ha)).symm
           _ = Real.exp (Real.log b + (j : ℝ)*Real.log p) := by congr 1; linarith
           _ = _ := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (Nat.cast_pos.mpr hb),
                         Real.exp_log (Nat.cast_pos.mpr hp.pos)]
    exact_mod_cast H
  have hb1 : b = 1 := by
    have hd : b ∣ a := ⟨p^j,he⟩
    exact (Nat.gcd_eq_right hd).symm.trans (show a.gcd b = 1 from hcop)
  rw [hb1,one_mul] at he
  have hj : j ≠ 0 := by rintro rfl; simp [hb1,he] at hne
  have hf : Squarefree (p^j) := he ▸ hs
  have hj1 := ((Nat.squarefree_pow_iff hp.ne_one hj).mp hf).2
  exact ⟨by simpa [hj1] using he,hb1⟩

private theorem squarefree_of_live_atom {N a b : ℕ} (h : atom N a b ≠ 0) :
    Squarefree a ∧ Squarefree b := by
  constructor
  · by_contra H
    exact h (by simp [atom,coeff,mobiusRealCoefficient,ArithmeticFunction.moebius_eq_zero_of_not_squarefree H])
  · by_contra H
    exact h (by simp [atom,coeff,mobiusRealCoefficient,ArithmeticFunction.moebius_eq_zero_of_not_squarefree H])

/-- A nonzero primitive spectral atom can resonate on the prime grid only in the
two orientations of the prime itself. -/
private theorem resonance {p N a b : ℕ} (hp : p.Prime) (hq : (a,b) ∈ primitiveRatioPairs N)
    (hn : atom N a b ≠ 0) :
    Real.cos ((Real.log a-Real.log b)*(2*Real.pi/Real.log p)) = 1 ↔
      (a,b) = (p,1) ∨ (a,b) = (1,p) := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨hAB,hcop,hne⟩ := mem_filter.mp hq
  obtain ⟨hA,hB⟩ := mem_product.mp hAB
  obtain ⟨has,hbs⟩ := squarefree_of_live_atom hn
  constructor
  · intro H
    obtain ⟨k,hk⟩ := (Real.cos_eq_one_iff _).mp H
    have hlog : Real.log a - Real.log b = (k : ℝ)*Real.log p := by
      have h' : (k : ℝ)*(2*Real.pi)*Real.log p = (Real.log a-Real.log b)*(2*Real.pi) := by
        rw [hk]
        field_simp [hlp.ne']
      apply mul_right_cancel₀ (show (2*Real.pi : ℝ) ≠ 0 by positivity)
      calc _ = (k : ℝ)*(2*Real.pi)*Real.log p := h'.symm
           _ = _ := by ring
    cases k with
    | ofNat j =>
      obtain ⟨ha,hb⟩ := positive_resonance hp (mem_Icc.mp hA).1 (mem_Icc.mp hB).1 hcop hne has hlog
      exact Or.inl (Prod.ext ha hb)
    | negSucc j =>
      have hh : Real.log b-Real.log a = ((j+1 : ℕ) : ℝ)*Real.log p := by
        push_cast at hlog ⊢
        linarith only [hlog]
      obtain ⟨hb,ha⟩ := positive_resonance hp (mem_Icc.mp hB).1 (mem_Icc.mp hA).1 hcop.symm hne.symm hbs hh
      exact Or.inr (Prod.ext ha hb)
  · rintro (he | he)
    · cases he
      rw [Nat.cast_one, Real.log_one, sub_zero, show Real.log p*(2*Real.pi/Real.log p)=2*Real.pi by field_simp]
      exact Real.cos_two_pi
    · cases he
      rw [Nat.cast_one, Real.log_one, zero_sub,
        show -Real.log p*(2*Real.pi/Real.log p)=-(2*Real.pi) by field_simp, Real.cos_neg, Real.cos_two_pi]

/-- Limit of positive binomial height averages at spacing `2π/log p`. Every
off-diagonal contribution except the prime and its reciprocal disappears. -/
theorem prime_grid_binomial_spectrum (N : ℕ) (p : Nat.Primes) (t : ℝ) :
    Tendsto (fun r : ℕ => (binomialHeightMean (2*Real.pi/Real.log p.val) ^ r)
      (fun x => ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint x)‖^2) t) atTop
      (𝓝 ((∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n) +
        ∑ q ∈ (primitiveRatioPairs N).filter (fun q => q = (p.val,1) ∨ q = (1,p.val)),
          atom N q.1 q.2 * Real.cos ((Real.log q.1-Real.log q.2)*t))) := by
  simp_rw [critical_power_binomial]
  rw [Finset.sum_filter]
  apply tendsto_const_nhds.add
  apply tendsto_finsetSum
  intro q hq
  by_cases hn : atom N q.1 q.2 = 0
  · simp [hn]
  · have H := ((keep_limit (Real.log q.1-Real.log q.2) (2*Real.pi/Real.log p.val)).const_mul
        (atom N q.1 q.2)).mul_const (Real.cos ((Real.log q.1-Real.log q.2)*t))
    simpa only [resonance p.property hq hn, mul_ite, ite_mul, mul_one, mul_zero, zero_mul] using H


end

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
