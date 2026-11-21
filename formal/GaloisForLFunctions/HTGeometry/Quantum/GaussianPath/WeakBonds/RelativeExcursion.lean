import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.EntryRate

/-! # First-excursion tails in units of the actual continuous mean entry spacing -/
open Filter MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open PrescribedTimes
noncomputable section

private theorem retained_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (B : Set ℝ) (x : ι → ℝ) (hx : x ∈ retainedSector S B)
    (i : ι) (hi : i ∉ S) : x i ∈ B := by
  have h := hx i (mem_univ i)
  change x i ∈ (if i ∈ S then univ else B) at h
  rwa [if_neg hi] at h

/-- An uncut onsite coefficient in [1,2] keeps the full coupling norm at least one. -/
theorem retained_coefficient_norm {n : ℕ} (a b : Fin (n+1)) (x : PrefixIndex n → ℝ)
    (hx : x ∈ retainedSector (cutSet a b) (Icc 1 2)) : 1 ≤ coefficientNorm x := by
  let site : Fin (n+2) × Fin 3 := (0,0)
  let i : PrefixIndex n := (pathCoeffEquiv n).symm (Sum.inl site)
  have h : x i ∈ Icc (1:ℝ) 2 :=
    retained_value (cutSet a b) (Icc 1 2) x hx i (onsite_not_in_cutSet a b site)
  have hnorm : x i ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (PrefixIndex n))‖ :=
    (le_abs_self (x i)).trans (abs_coord_le_norm (WithLp.toLp 2 x) i)
  exact h.1.trans hnorm

/-- The shorter of the true first crossing time and its first subsequent
half-budget wait, in the unit set by the spectral entry flux. -/
def fluxExcursion (n P : ℕ) (x : PrefixIndex n → ℝ) : ℝ :=
  emptyRate n (1/10) x * min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x)

private theorem relative_lower {n P : ℕ} {x : PrefixIndex n → ℝ} {b T : ℝ}
    (hb : 0 < b) (hfloor : ∀ y : PrefixIndex n → ℝ, b*coefficientNorm y ≤ emptyRate n (1/10) y)
    (hn : 1 ≤ coefficientNorm x) (hT : 0 < T)
    (hw : (1+1/b)*T < min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x))
    {q : ℝ} (hq : 0 < q) : T < fluxExcursion n P (q • x) := by
  let J (y : PrefixIndex n → ℝ) := min (crossingOrigin n P (9/80) y) (crossingWait n P (P/2) y)
  have hj : q*J (q • x)=J x := by
    dsimp only [J]
    rw [mul_min_of_nonneg _ _ hq.le,smul_crossingOrigin _ _ _ hq,smul_crossingWait _ _ _ hq]
  have hnorm : coefficientNorm (q • x) = q*coefficientNorm x := by
    change ‖q • (WithLp.toLp 2 x : EuclideanSpace ℝ (PrefixIndex n))‖=q*coefficientNorm x
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hq]
    rfl
  have hpos : 0 < J x := (mul_pos (add_pos zero_lt_one (one_div_pos.mpr hb)) hT).trans hw
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

private theorem retained_to_flux {n P : ℕ} (a b : Fin (n+1)) {β T : ℝ}
    (hβ : 0 < β) (ht : 0 < T)
    (hfloor : ∀ x : PrefixIndex n → ℝ, β*coefficientNorm x ≤ emptyRate n (1/10) x)
    (x : PrefixIndex n → ℝ) (hx : x ∈ retainedSector (cutSet a b) (Icc 1 2))
    (hw : (1+1/β)*T < min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x)) :
    T < fluxExcursion n P x ∧ ∀ r > (0:ℝ), T < fluxExcursion n P (atRadius r x) := by
  have hn : 1 ≤ coefficientNorm x := retained_coefficient_norm (n := n) a b x hx
  have hf (q : ℝ) (hq : 0 < q) : T < fluxExcursion n P (q • x) :=
    relative_lower (n := n) (P := P) (x := x) hβ hfloor hn ht hw hq
  refine ⟨by simpa only [one_smul] using hf 1 zero_lt_one,fun r hr => ?_⟩
  exact hf _ (div_pos hr (zero_lt_one.trans_le hn))

private theorem rescale_survival {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q : Set X) (J : X → ℝ) (F : ℝ → Set X) {c β : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (h : ∀ v ≥ (1:ℝ), c ≤ v^18*μ.real {x | x∈Q ∧ v*(1/1800) < J x})
    (hf : ∀ T > (0:ℝ), ∀ x ∈ Q, (1+1/β)*T < J x → x ∈ F T) :
    ∃ b > (0:ℝ), ∀ T ≥ (1:ℝ), b ≤ T^18*μ.real (F T) := by
  let L := 1800*(1+1/β)
  have hL : 1≤L := by dsimp only [L]; linarith only [one_div_pos.mpr hβ]
  refine ⟨c/L^18,div_pos hc (pow_pos (zero_lt_one.trans_le hL) _),?_⟩
  intro T ht
  have hv := one_le_mul_of_one_le_of_one_le hL ht
  have he : (L*T)*(1/1800)=(1+1/β)*T := by dsimp only [L]; ring
  have hsub : {x | x∈Q ∧ (L*T)*(1/1800) < J x} ⊆ F T :=
    fun x hx => hf T (zero_lt_one.trans_le ht) x hx.1 (he ▸ hx.2)
  have hm := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
  have hh := (h (L*T) hv).trans (mul_le_mul_of_nonneg_left hm (pow_nonneg (zero_le_one.trans hv) 18))
  rw [mul_pow] at hh
  apply (div_le_iff₀ (pow_pos (zero_lt_one.trans_le hL) 18)).mpr
  linarith only [hh]

private theorem retained_tail {n P : ℕ} (a b : Fin (n+1)) (μ : Measure (PrefixIndex n → ℝ))
    [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c)
    (h : ∀ v ≥ (1:ℝ), c ≤ v^18*μ.real {x | x ∈ retainedSector (cutSet a b) (Icc 1 2) ∧
      v*(1/1800) < min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x)}) :
    ∃ c' > (0:ℝ), ∀ T ≥ (1:ℝ), c' ≤ T^18*μ.real {x |
      T < fluxExcursion n P x ∧ ∀ r > (0:ℝ), T < fluxExcursion n P (atRadius r x)} := by
  have hs : (1/10:ℝ) < sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  obtain ⟨hβ,hfloor⟩ := coefficient_rate_floor n (1/10) (by norm_num) hs
  exact rescale_survival μ (retainedSector (cutSet a b) (Icc 1 2))
    (fun x => min (crossingOrigin n P (9/80) x) (crossingWait n P (P/2) x))
    (fun T => {x | T < fluxExcursion n P x ∧ ∀ r > (0:ℝ), T < fluxExcursion n P (atRadius r x)})
    hc hβ h (fun _ ht => retained_to_flux a b hβ ht hfloor)

/-- At fixed physical error 1/10, the true first excursion divided by the
mean empty-entry spacing has a power-law lower tail. The same exceptional
draws work at every positive radial normalization. -/
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
  have hp : 0 < (gaussianReal 0 1).real (Icc (1:ℝ) 2) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by norm_num : (1:ℝ) < 2)).ne' (measure_ne_top _ _)
  exact retained_tail (n := k+1) (P := P) a b μ
    (mul_pos (pow_pos (mul_pos zero_lt_two gaussianDensityFloor_pos) _) (pow_pos hp _))
    (fun v hv => h (Icc 1 2) measurableSet_Icc (P/2) le_rfl v hv)

#print axioms gaussian_relative_first_excursion_tail
end
end GaloisForLFunctions.HTGeometry.WeakBonds
