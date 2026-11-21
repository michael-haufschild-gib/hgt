import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.EntryRate

/-! # First-excursion tails in units of the actual continuous mean entry spacing -/
open Filter MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open PrescribedTimes
noncomputable section

private theorem retained_norm_one {n : ℕ} (a b : Fin (n+1)) (x : PrefixIndex n → ℝ)
    (hx : x ∈ retainedSector (cutSet a b) (Icc 1 2)) : 1 ≤ coefficientNorm x := by
  let site : Fin (n+2) × Fin 3 := (0,0)
  let i := (pathCoeffEquiv n).symm (Sum.inl site)
  have h := hx i (mem_univ i)
  change x i ∈ (if i ∈ cutSet a b then univ else Icc (1:ℝ) 2) at h
  rw [if_neg (onsite_not_in_cutSet a b site)] at h
  exact h.1.trans ((le_abs_self _).trans (abs_coord_le_norm (WithLp.toLp 2 x) i))

/-- The shorter of the true first crossing time and its first subsequent
half-budget wait, in the unit set by the spectral entry flux. -/
def fluxExcursion (n P : ℕ) (x : PrefixIndex n → ℝ) : ℝ :=
  emptyRate n (1/10) x * min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x)

private theorem relative_lower {n P : ℕ} {x : PrefixIndex n → ℝ} {b T : ℝ}
    (hb : 0<b) (hfloor : ∀ y : PrefixIndex n → ℝ, b*coefficientNorm y ≤ emptyRate n (1/10) y)
    (hn : 1 ≤ coefficientNorm x) (hT : 0<T)
    (hw : (1+1/b)*T < min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x))
    {q : ℝ} (hq : 0<q) : T < fluxExcursion n P (q • x) := by
  let J (y : PrefixIndex n → ℝ) := min (crossingOrigin n P (9/80) y) (crossingWait n P (P/2) y)
  have hj : q*J (q • x)=J x := by
    dsimp only [J]
    rw [mul_min_of_nonneg _ _ hq.le,smul_crossingOrigin _ _ _ hq,smul_crossingWait _ _ _ hq]
  have hnorm : coefficientNorm (q • x) = q*coefficientNorm x := by
    change ‖q • (WithLp.toLp 2 x : EuclideanSpace ℝ (PrefixIndex n))‖=q*coefficientNorm x
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hq]
    rfl
  have hpos : 0<J x := (mul_pos (add_pos zero_lt_one (one_div_pos.mpr hb)) hT).trans hw
  have hz : 0 < J (q • x) := pos_of_mul_pos_right (hj.symm ▸ hpos) hq.le
  have hscale : T ≤ b*((1+1/b)*T) := by
    rw [show b*((1+1/b)*T)=T+b*T by field_simp; ring]
    exact le_add_of_nonneg_right (mul_nonneg hb.le hT.le)
  have hrate : b*q ≤ emptyRate n (1/10) (q • x) := by
    have hf := hfloor (q • x)
    rw [hnorm] at hf
    exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hq.le hn) hb.le).trans hf
  calc
    T < b*J x := hscale.trans_lt (mul_lt_mul_of_pos_left hw hb)
    _ = (b*q)*J (q • x) := by rw [mul_assoc,hj]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrate hz.le

/-- At fixed physical error 1/10, no bounded multiple of the true mean
spacing bounds the first excursion on a full-measure set of draws. The
same positive-probability exceptions work at every positive radial
normalization. The constant depends on the prefix. -/
theorem gaussian_relative_first_excursion_tail :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∃ c > (0:ℝ), ∀ T ≥ (1:ℝ), c ≤ T^18*μ.real {x |
        T < fluxExcursion n P x ∧ ∀ r > (0:ℝ), T < fluxExcursion n P (atRadius r x)} := by
  filter_upwards [gaussian_two_weak_bonds_joint_survival] with k hg
  intro n P μ
  obtain ⟨a,b,_,h⟩ := hg
  let bulk := Icc (1:ℝ) 2
  let c := (2*gaussianDensityFloor)^18*(gaussianReal 0 1).real bulk^(cutSet a b)ᶜ.card
  have hp : 0 < (gaussianReal 0 1).real bulk :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by norm_num : (1:ℝ)<2)).ne' (measure_ne_top _ _)
  have hc : 0<c := mul_pos (pow_pos (mul_pos zero_lt_two gaussianDensityFloor_pos) _) (pow_pos hp _)
  let D : ℕ := 2^(n+2)
  let β := (SharpOccupation.physicalArc (1/10))^(D-2)*(D:ℝ)^2/(4*π*(Fintype.card (PathLabel n):ℝ))
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  obtain ⟨hβ,hfloor⟩ := coefficient_rate_floor n (1/10) (by norm_num) hs
  change 0<β at hβ
  let L := 1800*(1+1/β)
  have hL : 1≤L := by dsimp only [L]; linarith only [one_div_pos.mpr hβ]
  refine ⟨c/L^18,div_pos hc (pow_pos (zero_lt_one.trans_le hL) _),?_⟩
  intro T ht
  have hv : 1 ≤ L*T := one_le_mul_of_one_le_of_one_le hL ht
  have htail := h bulk measurableSet_Icc (P/2) le_rfl (L*T) hv
  let F := {x : PrefixIndex n → ℝ | T < fluxExcursion n P x ∧
    ∀ r > (0:ℝ), T < fluxExcursion n P (atRadius r x)}
  have hsub : {x | x ∈ retainedSector (cutSet a b) bulk ∧
      (L*T)*(1/1800) < min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x)} ⊆ F := by
    rintro x ⟨hx,hw⟩
    have hn := retained_norm_one a b x hx
    rw [show (L*T)*(1/1800)=(1+1/β)*T by dsimp only [L]; ring] at hw
    have hf := fun (q : ℝ) (hq : 0<q) => relative_lower hβ hfloor hn (zero_lt_one.trans_le ht) hw hq
    refine ⟨by simpa only [one_smul] using hf 1 zero_lt_one,fun r hr => ?_⟩
    exact hf _ (div_pos hr (zero_lt_one.trans_le hn))
  apply (div_le_iff₀ (pow_pos (zero_lt_one.trans_le hL) 18)).mpr
  have hh := htail.trans (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hsub (measure_ne_top _ _)) (pow_nonneg (zero_le_one.trans hv) _))
  rw [mul_pow] at hh
  change c ≤ (T^18*μ.real F)*L^18
  linarith only [hh]

#print axioms gaussian_relative_first_excursion_tail
end
end GaloisForLFunctions.HTGeometry.WeakBonds
