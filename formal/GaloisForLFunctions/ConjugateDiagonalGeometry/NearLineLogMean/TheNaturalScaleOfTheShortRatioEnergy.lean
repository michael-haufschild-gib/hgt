import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheShortRatioEnergyOfLongMoebiusPolynomials
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheHybridHeightBoundForSharpMoebiusSections

/-!
# The natural scale of the short-ratio energy

The p = 2 endpoint in Wu and Yang (arXiv:2611.05863) uses Plancherel
equality. On the real line this weights the sharp Möbius polynomial by the squared Fourier
transform of its logarithmic window. Frequencies up to T(N+1)² use
the hybrid height estimate. Above that cutoff the trivial coefficient
bound and the inverse-square Fourier tail together cost O(1/T).
This retains the factor 1/T from the physical window uniformly in N.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open Finset Complex MeasureTheory Filter Topology _root_.RHTower.Sieve
open _root_.RHTower hiding linePoint
open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg)
noncomputable section

private theorem logPoly_trivial (N : ℕ) (w : ℝ) :
    ‖logPoly (fun n => (coeff n:ℂ)) (Icc 1 N) w‖≤(N:ℝ)+1 := by
  rw [←critical_moebius_logPoly]
  let t := -(2*Real.pi)*w
  have he := _root_.RHTower.norm_edPoly_le _root_.RHTower.mobCoeff (s:=Icc 1 N)
    (fun _ hn => (mem_Icc.mp hn).1) (linePoint t)
  refine he.trans ?_
  calc
    _ ≤ ∑ _n ∈ Icc 1 N, (1:ℝ) := by
      apply sum_le_sum
      intro n hn
      have h₁ : (1:ℝ)≤n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [MultiscaleMollifiedZetaField.linePoint_re]
      exact mul_le_one₀ (_root_.RHTower.norm_mobCoeff_le _) (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos h₁ (by norm_num))
    _ ≤ _ := by simp [Nat.card_Icc]

/-- Uniform two-parameter estimate. Multiplying energy by inverse
bandwidth leaves only arbitrarily small height growth beyond the zero-width power. -/
theorem normalized_short_ratio_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ) (T : ℝ), 1≤T →
      T*bandEnergy N T⁻¹≤C*((N:ℝ)+1)^(2*zetaZeroWidth+ε)*T^ε := by
  have hwidth := zetaZeroWidth_nonneg
  let e := ε/8
  have he : 0<e := by dsimp only [e]; positivity
  obtain ⟨K,hK,hbound⟩ := hybrid_moebius_section_bound he
  let b := K*(2+2*Real.pi)^e
  have hb : 0≤b := mul_nonneg hK (Real.rpow_nonneg (by positivity) _)
  have hπ : 0<Real.pi^2 := by positivity
  refine ⟨b^2+2/Real.pi^2,by positivity,fun N T hT => ?_⟩
  let D := (N:ℝ)+1
  let W := T*D^2
  let A := b*D^(zetaZeroWidth+e)*W^e
  have hD : 1≤D := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hd := zero_lt_one.trans_le hD
  have ht := zero_lt_one.trans_le hT
  have hW : 1≤W := one_le_mul_of_one_le_of_one_le hT (one_le_pow₀ hD)
  have hw := zero_lt_one.trans_le hW
  have hlow (w : ℝ) (hw' : w∈Set.Icc (-W) W) :
      ‖logPoly (fun n => (coeff n:ℂ)) (Icc 1 N) w‖^2≤A^2 := by
    rw [←critical_moebius_logPoly]
    have ht' : 2+|-(2*Real.pi)*w|≤(2+2*Real.pi)*W := by
      rw [abs_mul,abs_neg,abs_of_pos (by positivity : 0<2*Real.pi)]
      have hh := mul_le_mul_of_nonneg_left (abs_le.mpr hw') (by positivity : 0≤2*Real.pi)
      linarith only [hh,hW]
    have hh := Real.rpow_le_rpow (by positivity) ht' he.le
    rw [Real.mul_rpow (by positivity) hw.le] at hh
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (hbound N _).trans ((mul_le_mul_of_nonneg_left hh (by positivity :
      0≤K*D^(zetaZeroWidth+e))).trans_eq (by dsimp only [A,b]; ring))
  have hhigh (w : ℝ) : ‖logPoly (fun n => (coeff n:ℂ)) (Icc 1 N) w‖^2≤D^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (logPoly_trivial N w) 2
  have hsplit := gallagher_split (fun n => (coeff n:ℂ)) (Icc 1 N) (inv_pos.mpr ht) hw
    (sq_nonneg A) (sq_nonneg D) hlow hhigh
  have hscale : A^2=b^2*D^(2*zetaZeroWidth+6*e)*T^(2*e) := by
    have hpow : (D^2)^e=D^(2*e) := by
      rw [←Real.rpow_natCast D 2,←Real.rpow_mul hd.le] <;> norm_num
    rw [show A=b*D^(zetaZeroWidth+e)*(T*D^2)^e from rfl,
      Real.mul_rpow ht.le (sq_nonneg D),hpow]
    calc
      _ = b^2*((D^(zetaZeroWidth+e)*D^(2*e))*(D^(zetaZeroWidth+e)*D^(2*e)))*(T^e*T^e) := by ring
      _ = _ := by
        simp only [←Real.rpow_add hd,←Real.rpow_add ht]
        ring_nf
  have ha : A^2≤b^2*D^(2*zetaZeroWidth+ε)*T^ε := by
    rw [hscale]
    have h₁ : 2*zetaZeroWidth+6*e≤2*zetaZeroWidth+ε := by dsimp only [e]; linarith
    have h₂ : 2*e≤ε := by dsimp only [e]; linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD h₁) (sq_nonneg _))
      (Real.rpow_le_rpow_of_exponent_le hT h₂) (Real.rpow_nonneg ht.le _)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hd.le _))
  have hfac : 1≤D^(2*zetaZeroWidth+ε)*T^ε :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hD (by positivity)) (Real.one_le_rpow hT hε.le)
  calc
    _ ≤ T*(A^2*T⁻¹+D^2*(2/(Real.pi^2*W))) := mul_le_mul_of_nonneg_left hsplit ht.le
    _ = A^2+2/Real.pi^2 := by dsimp only [W]; field_simp [ht.ne',hd.ne',Real.pi_ne_zero]
    _ ≤ b^2*D^(2*zetaZeroWidth+ε)*T^ε+(2/Real.pi^2)*(D^(2*zetaZeroWidth+ε)*T^ε) :=
      add_le_add ha (le_mul_of_one_le_right (by positivity) hfac)
    _ = _ := by ring

/-- In power-length windows the physical energy has height exponent
−1+2θ times the zero width contribution, up to every positive loss. -/
theorem short_ratio_bound_with_bandwidth {θ ε : ℝ} (hθ : 0<θ) (hε : 0<ε) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T →
      bandEnergy ⌊T^θ⌋₊ T⁻¹≤C*T^(-1+2*zetaZeroWidth*θ+ε) := by
  let e := ε/(θ+1)
  have hp : 0<θ+1 := by positivity
  have he : 0<e := div_pos hε hp
  obtain ⟨K,hK,hbound⟩ := normalized_short_ratio_bound he
  let r := 2*zetaZeroWidth+e
  have hr : 0≤r := add_nonneg (mul_nonneg (by norm_num) zetaZeroWidth_nonneg) he.le
  refine ⟨K*2^r,by positivity,fun T hT => ?_⟩
  have ht := zero_lt_one.trans_le hT
  have hN : (⌊T^θ⌋₊:ℝ)+1≤2*T^θ := by
    linarith only [Nat.floor_le (Real.rpow_nonneg ht.le θ),Real.one_le_rpow hT hθ.le]
  have hh := hbound ⌊T^θ⌋₊ T hT
  have hpow := Real.rpow_le_rpow (by positivity) hN hr
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg ht.le _),←Real.rpow_mul ht.le] at hpow
  apply (mul_le_mul_iff_right₀ ht).mp
  refine hh.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) (by positivity :
    0≤T^e)).trans_eq ?_)
  have hidx : θ*r+e=1+(-1+2*zetaZeroWidth*θ+ε) := by
    dsimp only [r,e]
    field_simp [hp.ne']
    ring
  calc
    _ = (K*2^r)*(T^(θ*r)*T^e) := by ring
    _ = _ := by rw [←Real.rpow_add ht,hidx,Real.rpow_add ht,Real.rpow_one]; ring

end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
