import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivityConverse
import GaloisForLFunctions.RHTower.WeilLagFunctionHerglotz
import GaloisForLFunctions.RHTower.ReflectionTateParity
import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand
import GaloisForLFunctions.RHTower.GaussHodgeSeamEnergyBridge

/-!
# The per-zero cone criterion for slice Taylor positivity

Pair every zero copy `ρ` with its Hermitian reflection `1 − ρ̄` (`lagPartner`), which has the same
ordinate.  In the centred variable the reflection is complex conjugation of the spectral point
`z = (ρ − ½)(−i) = a + ci`, with `a = Im ρ` and `c = ½ − Re ρ`.  At height `t` the four Weierstrass
factors of the pair multiply to

  `e^{4ta/(a²+c²)}/(a²+c²)² · (x⁴ + 2((a−t)² − c²)x² + ((a−t)² + c²)²)`,

and a critical copy (`c = 0`) contributes `e^{2t/a}((a−t)² + x²)/a²`.  So the pair has nonnegative
Taylor coefficients exactly when `|Re ρ − ½| ≤ |Im ρ − t|`: the zero lies outside the cone of
half-angle `π/4` at height `t`.

Theorem: if every zero copy lies outside the cone at height `t`, every slice Taylor coefficient at
`t` is nonnegative.  The proof groups the Hadamard product into reflection orbits along
reflection-closed finite sets and passes to the locally uniform limit.  This localises
`riemannHypothesis_iff_xiSliceCoeff_nonneg`: only zeros with `|Im ρ − t| < |Re ρ − ½|` can break
positivity at `t`.

With the unconditional critical-line band below squared ordinate `2365/16` the cone condition holds
for `|t| ≤ 233/20`, so every higher Laguerre expression of `Ξ` is nonnegative there, unconditionally.
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The Hermitian reflection is an involution on divisor copies. -/
theorem lagPartner_lagPartner (q : XiZeroCopy) : lagPartner (lagPartner q) = q := by
  have hfst : (lagPartner (lagPartner q)).1 = q.1 := Subtype.ext (lagPartner_fst_involutive q)
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
  simp [lagPartner, xiZeroCopyConjEquiv, xiZeroCopyReflectEquiv, xiZeroConjEquiv,
    xiZeroReflectEquiv, Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

/-- The reflection conjugates the spectral point. -/
theorem xiSpectralPoint_lagPartner (q : XiZeroCopy) :
    xiSpectralPoint (lagPartner q) = (starRingEnd ℂ) (xiSpectralPoint q) := by
  rw [xiSpectralPoint, xiSpectralPoint, lagPartner_coe, map_mul, map_sub, map_neg,
    Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

/-- Index-map composition of locally uniform convergence. -/
theorem tendstoLocallyUniformlyOn_comp_index {ι κ α β : Type*} [TopologicalSpace α]
    [UniformSpace β] {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter κ} {s : Set α}
    (h : TendstoLocallyUniformlyOn F f p s) {φ : κ → ι} (hφ : Tendsto φ q p) :
    TendstoLocallyUniformlyOn (fun k => F (φ k)) f q s := by
  intro u hu x hx
  obtain ⟨t, ht, H⟩ := h u hu x hx
  exact ⟨t, ht, hφ.eventually H⟩

/-- Taylor positivity of a finite product grouped into orbits of an involution. -/
theorem nonnegTaylorAtZero_prod_of_involution {α : Type*} [DecidableEq α] (σ : α → α)
    (hσ : ∀ a, σ (σ a) = a) (f : α → ℂ → ℂ)
    (hfix : ∀ a, σ a = a → NonnegTaylorAtZero (f a))
    (hpair : ∀ a, σ a ≠ a → NonnegTaylorAtZero (f a * f (σ a))) :
    ∀ S : Finset α, (∀ a ∈ S, σ a ∈ S) → NonnegTaylorAtZero (fun x => ∏ a ∈ S, f a x) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with hE | ⟨a, ha⟩
    · subst hE
      simpa using nonnegTaylorAtZero_const (zero_le_one : (0 : ℂ) ≤ 1)
    by_cases hfa : σ a = a
    · set T := S.erase a with hT
      have hTS : T ⊂ S := Finset.erase_ssubset ha
      have hTc : ∀ b ∈ T, σ b ∈ T := by
        intro b hb
        rw [hT, Finset.mem_erase] at hb ⊢
        refine ⟨fun h => hb.1 ?_, hS b hb.2⟩
        rw [← hσ b, h, hfa]
      have e : (fun x => ∏ b ∈ S, f b x) = f a * fun x => ∏ b ∈ T, f b x := by
        funext x
        rw [Pi.mul_apply, hT, Finset.mul_prod_erase S (fun b => f b x) ha]
      rw [e]
      exact (hfix a hfa).mul (ih T hTS hTc)
    · have hσa : σ a ∈ S.erase a := Finset.mem_erase.mpr ⟨hfa, hS a ha⟩
      set T := (S.erase a).erase (σ a) with hT
      have hTS : T ⊂ S :=
        (Finset.erase_ssubset hσa).trans_le (Finset.erase_subset a S)
      have hTc : ∀ b ∈ T, σ b ∈ T := by
        intro b hb
        rw [hT, Finset.mem_erase, Finset.mem_erase] at hb ⊢
        exact ⟨fun h => hb.2.1 (by rw [← hσ b, h, hσ]), fun h => hb.1 (by rw [← hσ b, h]),
          hS b hb.2.2⟩
      have e : (fun x => ∏ b ∈ S, f b x) = (f a * f (σ a)) * fun x => ∏ b ∈ T, f b x := by
        funext x
        rw [Pi.mul_apply, Pi.mul_apply, hT,
          ← Finset.mul_prod_erase S (fun b => f b x) ha,
          ← Finset.mul_prod_erase (S.erase a) (fun b => f b x) hσa]
        ring
      rw [e]
      exact (hpair a hfa).mul (ih T hTS hTc)

/-- The paired Weierstrass factor at a complex spectral point `z`. -/
theorem weierstrassE1_slice_pair_complex {z : ℂ} (hz : z ≠ 0) (t : ℝ) (x : ℂ) :
    weierstrassE1 (((t : ℂ) - I * x) / z) * weierstrassE1 (((t : ℂ) + I * x) / z) =
      ((z - t) ^ 2 + x ^ 2) / z ^ 2 * cexp (2 * t / z) := by
  unfold weierstrassE1
  have hexp : cexp (((t : ℂ) - I * x) / z) * cexp (((t : ℂ) + I * x) / z) = cexp (2 * t / z) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring
  calc (1 - ((t : ℂ) - I * x) / z) * cexp (((t : ℂ) - I * x) / z) *
        ((1 - ((t : ℂ) + I * x) / z) * cexp (((t : ℂ) + I * x) / z))
      = (1 - ((t : ℂ) - I * x) / z) * (1 - ((t : ℂ) + I * x) / z) *
          (cexp (((t : ℂ) - I * x) / z) * cexp (((t : ℂ) + I * x) / z)) := by ring
    _ = _ := by
      rw [hexp]
      field_simp
      linear_combination (-(x ^ 2)) * Complex.I_sq

/-- The quartic of a reflection pair. -/
theorem slice_reflectionPair_poly (a c t : ℝ) (x : ℂ) :
    (((a : ℂ) + c * I - t) ^ 2 + x ^ 2) * (((a : ℂ) - c * I - t) ^ 2 + x ^ 2) =
      x ^ 4 + ((2 * ((a - t) ^ 2 - c ^ 2) : ℝ) : ℂ) * x ^ 2 + ((((a - t) ^ 2 + c ^ 2) ^ 2 : ℝ) : ℂ) := by
  push_cast
  linear_combination ((c : ℂ) ^ 2 * (2 * x ^ 2 - 2 * ((a : ℂ) - t) ^ 2 + (c : ℂ) ^ 2 * I ^ 2 -
    (c : ℂ) ^ 2)) * Complex.I_sq

/-- The four-factor reflection pair at `z = a + ci` is a nonnegative multiple of
`x⁴ + 2((a−t)² − c²)x² + ((a−t)² + c²)²`. -/
theorem weierstrassE1_slice_reflectionPair {a c t : ℝ} (hz : (a : ℂ) + c * I ≠ 0) (x : ℂ) :
    (weierstrassE1 (((t : ℂ) - I * x) / ((a : ℂ) + c * I)) *
        weierstrassE1 (((t : ℂ) + I * x) / ((a : ℂ) + c * I))) *
      (weierstrassE1 (((t : ℂ) - I * x) / (starRingEnd ℂ ((a : ℂ) + c * I))) *
        weierstrassE1 (((t : ℂ) + I * x) / (starRingEnd ℂ ((a : ℂ) + c * I)))) =
      ((Real.exp (4 * t * a / (a ^ 2 + c ^ 2)) / (a ^ 2 + c ^ 2) ^ 2 : ℝ) : ℂ) *
        (x ^ 4 + ((2 * ((a - t) ^ 2 - c ^ 2) : ℝ) : ℂ) * x ^ 2 +
          ((((a - t) ^ 2 + c ^ 2) ^ 2 : ℝ) : ℂ)) := by
  have hconj : starRingEnd ℂ ((a : ℂ) + c * I) = (a : ℂ) - c * I := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hz' : (a : ℂ) - c * I ≠ 0 := by
    rw [← hconj]
    exact (map_ne_zero _).mpr hz
  have hnorm : (a : ℝ) ^ 2 + c ^ 2 ≠ 0 := by
    intro h0
    apply hz
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg c]
    simp [ha, hc]
  have hnormc : ((a : ℂ) ^ 2 + (c : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hnorm
  have hprod : ((a : ℂ) + c * I) * ((a : ℂ) - c * I) = (a : ℂ) ^ 2 + (c : ℂ) ^ 2 := by
    linear_combination (-(c : ℂ) ^ 2) * Complex.I_sq
  rw [hconj, weierstrassE1_slice_pair_complex hz, weierstrassE1_slice_pair_complex hz']
  have hexp : cexp (2 * t / ((a : ℂ) + c * I)) * cexp (2 * t / ((a : ℂ) - c * I)) =
      ((Real.exp (4 * t * a / (a ^ 2 + c ^ 2)) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
    linear_combination (4 * (t : ℂ) * a) * hprod + (8 * (t : ℂ) * a * (c : ℂ) ^ 2) * Complex.I_sq
  have hsplit : ∀ z w E F : ℂ, ((z - t) ^ 2 + x ^ 2) / z ^ 2 * E * (((w - t) ^ 2 + x ^ 2) / w ^ 2 * F) =
      (((z - t) ^ 2 + x ^ 2) * ((w - t) ^ 2 + x ^ 2)) / (z * w) ^ 2 * (E * F) := by
    intros
    ring
  rw [hsplit, slice_reflectionPair_poly, hprod, hexp]
  push_cast
  field_simp

/-- A nonnegative multiple of a quartic `x⁴ + Px² + Q` with `P, Q ≥ 0`. -/
theorem nonnegTaylorAtZero_quartic {C P Q : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    NonnegTaylorAtZero (fun x => (C : ℂ) * (x ^ 4 + (P : ℂ) * x ^ 2 + (Q : ℂ))) := by
  have e : (fun x : ℂ => (C : ℂ) * (x ^ 4 + (P : ℂ) * x ^ 2 + (Q : ℂ))) =
      (fun _ => (C : ℂ)) * (((((fun x : ℂ => x) * fun x => x) * fun x => x) * fun x => x) +
        ((fun _ => (P : ℂ)) * ((fun x : ℂ => x) * fun x => x)) + fun _ => (Q : ℂ)) := by
    funext x
    simp only [Pi.mul_apply, Pi.add_apply]
    ring
  rw [e]
  have hid := nonnegTaylorAtZero_id
  have c0 : ∀ {r : ℝ}, 0 ≤ r → NonnegTaylorAtZero (fun _ => (r : ℂ)) := fun h =>
    nonnegTaylorAtZero_const (Complex.zero_le_real.mpr h)
  exact (c0 hC).mul ((((((hid.mul hid).mul hid).mul hid).add ((c0 hP).mul (hid.mul hid)))).add
    (c0 hQ))

/-- The spectral point in real coordinates: `z_q = Im ρ + (½ − Re ρ) i`. -/
theorem xiSpectralPoint_eq_re_im (q : XiZeroCopy) :
    xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) + (((1 / 2 - (q.1 : ℂ).re : ℝ)) : ℂ) * I := by
  apply Complex.ext <;> simp [xiSpectralPoint, Complex.mul_re, Complex.mul_im]

/-- **Per-zero cone criterion.**  If every zero copy satisfies `|Re ρ − ½| ≤ |Im ρ − t|`, every
Taylor coefficient of the slice product at height `t` is nonnegative. -/
theorem nonnegTaylorAtZero_xiSliceProduct_of_cone {t : ℝ}
    (hcone : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q.1 : ℂ).im - t|) :
    NonnegTaylorAtZero (xiSliceProduct t) := by
  classical
  set φm : ℂ → ℂ := fun x => (t : ℂ) - I * x with hφm
  set φp : ℂ → ℂ := fun x => (t : ℂ) + I * x with hφp
  have hcm : Continuous φm := by rw [hφm]; fun_prop
  have hcp : Continuous φp := by rw [hφp]; fun_prop
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hPcont : Continuous xiCanonicalProduct :=
    continuous_iff_continuousAt.mpr fun z =>
      (xiCanonicalProduct_analytic z (Set.mem_univ z)).continuousAt
  have hPdiff : Differentiable ℂ xiCanonicalProduct := fun z =>
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hm := TendstoLocallyUniformlyOn.comp hP φm (Set.mapsTo_univ φm Set.univ) hcm.continuousOn
  have hp := TendstoLocallyUniformlyOn.comp hP φp (Set.mapsTo_univ φp Set.univ) hcp.continuousOn
  have hmul := hm.mul₀ hp (hPcont.comp hcm).continuousOn (hPcont.comp hcp).continuousOn
  let c : Finset XiZeroCopy → Finset XiZeroCopy := fun S => S ∪ S.image lagPartner
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun S => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ S, ∀ a ∈ c S, lagPartner a ∈ c S := by
    intro S a ha
    simp only [c, Finset.mem_union, Finset.mem_image] at ha ⊢
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · left
      rw [lagPartner_lagPartner]
      exact hb
  have hmul' := tendstoLocallyUniformlyOn_comp_index hmul hc
  set f : XiZeroCopy → ℂ → ℂ := fun q x =>
    weierstrassE1 (φm x / xiSpectralPoint q) * weierstrassE1 (φp x / xiSpectralPoint q) with hf
  have hfix : ∀ q, lagPartner q = q → NonnegTaylorAtZero (f q) := by
    intro q hq
    have hre : (q.1 : ℂ).re = 1 / 2 := (lagPartner_fst_eq_iff q).mp (congrArg (fun r => (r.1 : ℂ)) hq)
    have hz : xiSpectralPoint q = (((q.1 : ℂ).im : ℝ) : ℂ) := by
      rw [xiSpectralPoint_eq_re_im, hre]
      simp
    have hγ : (q.1 : ℂ).im ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q
      rw [hz, h0, Complex.ofReal_zero]
    simp only [hf, hz, hφm, hφp]
    exact nonnegTaylorAtZero_slice_pair hγ
  have hpair : ∀ q, lagPartner q ≠ q → NonnegTaylorAtZero (f q * f (lagPartner q)) := by
    intro q _
    set a : ℝ := (q.1 : ℂ).im with ha
    set cc : ℝ := 1 / 2 - (q.1 : ℂ).re with hcc
    have hz : xiSpectralPoint q = (a : ℂ) + cc * I := xiSpectralPoint_eq_re_im q
    have hz0 : (a : ℂ) + cc * I ≠ 0 := by rw [← hz]; exact xiSpectralPoint_ne_zero q
    have hzσ : xiSpectralPoint (lagPartner q) = starRingEnd ℂ ((a : ℂ) + cc * I) := by
      rw [xiSpectralPoint_lagPartner, hz]
    have e : f q * f (lagPartner q) = fun x =>
        ((Real.exp (4 * t * a / (a ^ 2 + cc ^ 2)) / (a ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ) *
          (x ^ 4 + ((2 * ((a - t) ^ 2 - cc ^ 2) : ℝ) : ℂ) * x ^ 2 +
            ((((a - t) ^ 2 + cc ^ 2) ^ 2 : ℝ) : ℂ)) := by
      funext x
      simp only [Pi.mul_apply, hf, hz, hzσ, hφm, hφp]
      exact weierstrassE1_slice_reflectionPair hz0 x
    rw [e]
    have hsq : cc ^ 2 ≤ (a - t) ^ 2 := by
      have h := hcone q
      have h' : |cc| ≤ |a - t| := by
        rw [hcc, ha, abs_sub_comm]
        simpa using h
      exact sq_le_sq.mpr h'
    exact nonnegTaylorAtZero_quartic (by positivity) (by nlinarith) (by positivity)
  have hfin : ∀ S : Finset XiZeroCopy, NonnegTaylorAtZero
      (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φp)) := by
    intro S
    have e : (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) (c S) ∘ φp)) =
        fun x => ∏ q ∈ c S, f q x := by
      funext x
      simp only [Pi.mul_apply, Function.comp_apply, hf]
      rw [Finset.prod_mul_distrib]
    rw [e]
    exact nonnegTaylorAtZero_prod_of_involution lagPartner lagPartner_lagPartner f hfix hpair
      (c S) (hclosed S)
  have hlim : NonnegTaylorAtZero ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) :=
    NonnegTaylorAtZero.of_tendstoLocallyUniformlyOn hfin
      ((hPdiff.comp (by rw [hφm]; fun_prop)).mul (hPdiff.comp (by rw [hφp]; fun_prop))) hmul'
  have e : xiSliceProduct t = (fun _ => XiC 0 * XiC 0) *
      ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) := by
    funext x
    rw [xiSliceProduct_eq_XiC]
    have hX : ∀ a, XiC a = XiC 0 * xiCanonicalProduct a := fun a => by
      simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct a
    simp only [Pi.mul_apply, Function.comp_apply, hφm, hφp]
    rw [hX ((t : ℂ) - I * x), hX ((t : ℂ) + I * x)]
    ring
  rw [e]
  exact (nonnegTaylorAtZero_const zero_le_XiC_zero_mul_self).mul hlim

theorem xiSliceCoeff_nonneg_of_cone {t : ℝ}
    (hcone : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q.1 : ℂ).im - t|) (n : ℕ) :
    0 ≤ xiSliceCoeff t n := by
  unfold xiSliceCoeff
  have hfac : ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) := by push_cast; rfl
  rw [hfac]
  exact mul_nonneg (Complex.zero_le_real.mpr (by positivity))
    ((nonnegTaylorAtZero_xiSliceProduct_of_cone hcone).2 n)

/-- **Unconditional all-order slice positivity on a height band.**  For `|t| ≤ 233/20`, every
Taylor coefficient of `ξ(½+x+it)ξ(½−x+it)` at `0` (every higher Laguerre expression of `Ξ` at
`t`) is nonnegative. -/
theorem xiSliceCoeff_nonneg_of_abs_le {t : ℝ} (ht : |t| ≤ 233 / 20) (n : ℕ) :
    0 ≤ xiSliceCoeff t n := by
  refine xiSliceCoeff_nonneg_of_cone (fun q => ?_) n
  by_cases hh : (q.1 : ℂ).im ^ 2 < 2365 / 16
  · rw [xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hh, sub_self, abs_zero]
    exact abs_nonneg _
  · push Not at hh
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have h1 : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 := by
      rw [abs_lt]
      constructor <;> linarith [hstrip.1, hstrip.2]
    have h2 : (243 / 20 : ℝ) ≤ |(q.1 : ℂ).im| := by
      by_contra h
      push Not at h
      have habs := abs_nonneg ((q.1 : ℂ).im)
      have hsq : (q.1 : ℂ).im ^ 2 = |(q.1 : ℂ).im| ^ 2 := (sq_abs _).symm
      nlinarith
    have h3 := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) t
    linarith

end

end RHTower
