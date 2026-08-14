import GaloisForLFunctions.RHTower.ConvexDomainEulerCompleteness
import GaloisForLFunctions.RHTower.CompactCarrierFECompleteness
import GaloisForLFunctions.HTGeometry.ReflectedCarrierFunctional
import GaloisForLFunctions.HTGeometry.CauchyTransformGluingVertical
import GaloisForLFunctions.HTGeometry.ConvexCompactComplementConnected

/-!
# Functional-equation-symmetrised Euler tangents are complete right of the critical line

On a convex domain strictly between `Re s = 1/2` and `Re s = 1` the symmetrised tangents
`u_p(s) = w_p(s) - w_p(1-s)` are complete.  A continuous functional there is carried by a compact
convex `K` in the domain; reflecting the carrier in the critical line produces a second carrier
`1 - K` disjoint from it, and the difference of the functional and its reflected pullback kills the
symmetrised tangents.  The Lambert–Möbius sector argument then makes that difference kill every
power of the coordinate, so its Cauchy transform vanishes on the vertical strip separating the two
carriers; the two transforms are opposite there, glue to a bounded entire function, and Liouville
kills both.  Cauchy–Pompeiu turns the vanishing transform into annihilation of every holomorphic
function on the domain.

* `RHTower.feEulerTangentOn`;
* `RHTower.holoOn_eq_zero_of_annihilates_feEulerTangent`;
* `RHTower.topologicalClosure_span_feEulerTangentOn_eq_top`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The open strip strictly between the critical line and the abscissa of absolute convergence. -/
def rightCriticalStrip : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1}

theorem isOpen_rightCriticalStrip : IsOpen rightCriticalStrip := by
  have h₁ : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h₂ : IsOpen {s : ℂ | s.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hEq : rightCriticalStrip = {s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.re < 1} := rfl
  rw [hEq]
  exact h₁.inter h₂

theorem convex_rightCriticalStrip : Convex ℝ rightCriticalStrip :=
  (convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_re_lt 1)

/-- The symmetrised Euler tangent is holomorphic on the whole open critical strip. -/
theorem differentiableOn_feEulerTangent_strip {p : ℕ} (hp : p.Prime) :
    DifferentiableOn ℂ (feEulerTangent p) {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  have hsub : {s : ℂ | 0 < s.re ∧ s.re < 1} ⊆ {s : ℂ | 0 < s.re} := fun s hs => hs.1
  have hrefl : DifferentiableOn ℂ (fun s : ℂ => eulerTangent p (1 - s))
      {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    have hmap : Set.MapsTo (fun s : ℂ => 1 - s) {s : ℂ | 0 < s.re ∧ s.re < 1}
        {s : ℂ | 0 < s.re} := by
      intro s hs
      have h2 := hs.2
      simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.one_re]
      linarith
    exact (differentiableOn_eulerTangent hp).comp
      ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id) hmap
  exact ((differentiableOn_eulerTangent hp).mono hsub).sub hrefl

variable {D : Set ℂ}

theorem strip_subset_openStrip (hD : D ⊆ rightCriticalStrip) :
    D ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro z hz
  exact ⟨by linarith [(hD hz).1], (hD hz).2⟩

/-- The symmetrised Euler tangent on a domain right of the critical line. -/
def feEulerTangentMapOn (D : Set ℂ) (hD : D ⊆ rightCriticalStrip) (p : Nat.Primes) : C(D, ℂ) :=
  ⟨fun z => feEulerTangent (p : ℕ) (z : ℂ),
    ((differentiableOn_feEulerTangent_strip p.2).continuousOn.mono
      (strip_subset_openStrip hD)).restrict⟩

theorem feEulerTangentMapOn_mem (D : Set ℂ) (hD : D ⊆ rightCriticalStrip) (p : Nat.Primes) :
    feEulerTangentMapOn D hD p ∈ holoOn D :=
  ⟨feEulerTangent (p : ℕ),
    (differentiableOn_feEulerTangent_strip p.2).mono (strip_subset_openStrip hD), fun _ => rfl⟩

/-- The symmetrised Euler tangent as an element of the holomorphic space of the domain. -/
def feEulerTangentOn (D : Set ℂ) (hD : D ⊆ rightCriticalStrip) (p : Nat.Primes) : holoOn D :=
  ⟨feEulerTangentMapOn D hD p, feEulerTangentMapOn_mem D hD p⟩

section Carrier

variable {K : Set ℂ} [CompactSpace K]

/-- The reflection of a carrier in the critical line. -/
def reflCarrier (K : Set ℂ) : Set ℂ := (fun z : ℂ => 1 - z) '' K

theorem mem_reflCarrier {K : Set ℂ} {z : ℂ} : z ∈ reflCarrier K ↔ 1 - z ∈ K := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨1 - z, h, by ring⟩

theorem isCompact_reflCarrier {K : Set ℂ} (hK : IsCompact K) : IsCompact (reflCarrier K) :=
  hK.image (by fun_prop)

theorem one_sub_mem_reflCarrier {K : Set ℂ} {z : ℂ} (hz : z ∈ K) : 1 - z ∈ reflCarrier K :=
  ⟨z, hz, rfl⟩

end Carrier

section Completeness

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Cofinite annihilation of the symmetrised Euler tangents kills every continuous functional on
a convex domain right of the critical line.** -/
theorem holoOn_eq_zero_of_annihilates_feEulerTangent
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hD : D ⊆ rightCriticalStrip)
    (S : Finset Nat.Primes) (ell : holoOn D →L[ℝ] ℝ)
    (hann : ∀ p : Nat.Primes, p ∉ S →
      ell (feEulerTangentOn D hD p) = 0 ∧ ell (holoOnImul D (feEulerTangentOn D hD p)) = 0) :
    ∀ y : holoOn D, ell y = 0 := by
  classical
  obtain ⟨K₀, C₀, hK₀, hC₀, hbnd⟩ := exists_compact_dual_bound (holoOn D) ell
  set K₁ : Set ℂ := (Subtype.val : ↥D → ℂ) '' K₀ with hK₁def
  have hK₁ : IsCompact K₁ := hK₀.image continuous_subtype_val
  have hK₁D : K₁ ⊆ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨K, hKcompact, hKconv, hK₁K, hKD⟩ :=
    exists_compact_convex_between hK₁ hDopen hDconv hK₁D
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  -- strip and size bounds of the carrier
  obtain ⟨a, ha, haK⟩ : ∃ a : ℝ, 1 / 2 < a ∧ ∀ z ∈ K, a ≤ z.re := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨3 / 4, by norm_num, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMinOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => z.re))
      exact ⟨z₀.re, (hD (hKD hz₀K)).1, fun z hz => hz₀ hz⟩
  obtain ⟨b, hb, hbK⟩ : ∃ b : ℝ, b < 1 ∧ ∀ z ∈ K, z.re ≤ b := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨3 / 4, by norm_num, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMaxOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => z.re))
      exact ⟨z₀.re, (hD (hKD hz₀K)).2, fun z hz => hz₀ hz⟩
  obtain ⟨R, hRnn, hRK⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ‖z‖ ≤ R := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨0, le_rfl, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMaxOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => ‖z‖))
      exact ⟨‖z₀‖, norm_nonneg _, fun z hz => hz₀ hz⟩
  -- the reflected carrier and the union
  set K' : Set ℂ := reflCarrier K with hK'def
  have hK'compact : IsCompact K' := isCompact_reflCarrier hKcompact
  haveI : CompactSpace K' := isCompact_iff_compactSpace.mp hK'compact
  set Ktot : Set ℂ := K ∪ K' with hKtotdef
  have hKtotcompact : IsCompact Ktot := hKcompact.union hK'compact
  haveI : CompactSpace Ktot := isCompact_iff_compactSpace.mp hKtotcompact
  have hKKtot : K ⊆ Ktot := Set.subset_union_left
  have hK'Ktot : K' ⊆ Ktot := Set.subset_union_right
  have hmapKK' : ∀ z ∈ K, 1 - z ∈ K' := fun z hz => one_sub_mem_reflCarrier hz
  have hK'a : ∀ z ∈ K', z.re ≤ 1 - a := by
    intro z hz
    rw [hK'def, mem_reflCarrier] at hz
    have h := haK _ hz
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have hK'b : ∀ z ∈ K', 1 - b ≤ z.re := by
    intro z hz
    rw [hK'def, mem_reflCarrier] at hz
    have h := hbK _ hz
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have hK'R : ∀ z ∈ K', ‖z‖ ≤ 1 + R := by
    intro z hz
    rw [hK'def, mem_reflCarrier] at hz
    have h := hRK _ hz
    have hz' : z = 1 - (1 - z) := by ring
    rw [hz']
    calc ‖1 - (1 - z)‖ ≤ ‖(1 : ℂ)‖ + ‖1 - z‖ := norm_sub_le _ _
      _ ≤ 1 + R := by simpa using h
  set alpha : ℝ := min a (1 - b) with halphadef
  have halpha : 0 < alpha := lt_min (by linarith) (by linarith)
  have hKtotre : ∀ z ∈ Ktot, alpha ≤ z.re := by
    rintro z (hz | hz)
    · exact le_trans (min_le_left _ _) (haK z hz)
    · exact le_trans (min_le_right _ _) (hK'b z hz)
  have hKtotR : ∀ z ∈ Ktot, ‖z‖ ≤ 1 + R := by
    rintro z (hz | hz)
    · exact le_trans (hRK z hz) (by linarith)
    · exact hK'R z hz
  obtain ⟨M, hMK⟩ : ∃ M : ℝ, ∀ z ∈ Ktot, |z.im| ≤ M := by
    rcases Ktot.eq_empty_or_nonempty with hemp | hne
    · exact ⟨0, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKtotcompact.exists_isMaxOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => |z.im|))
      exact ⟨|z₀.im|, fun z hz => hz₀ hz⟩
  -- the complexified functional on the carrier
  set T : holoOn D →ₗ[ℝ] C(K, ℂ) := holoOnRestrict hKD with hT
  have hbd : ∀ g : holoOn D, |ell.toLinearMap g| ≤ C₀ * ‖T g‖ := by
    intro g
    refine hbnd g ‖T g‖ (norm_nonneg _) ?_
    intro x hx
    have hmem : ((x : ℂ)) ∈ K := hK₁K ⟨x, hx, rfl⟩
    have hxeq : (⟨(x : ℂ), hKD hmem⟩ : (D : Set ℂ)) = x := Subtype.ext rfl
    have hval : (g : C((D : Set ℂ), ℂ)) x = T g ⟨(x : ℂ), hmem⟩ := by
      rw [hT, holoOnRestrict_apply, hxeq]
    rw [hval]
    exact (T g).norm_coe_le_norm _
  obtain ⟨A, hA⟩ := exists_complex_functional_of_bound (M := ↥(holoOn D)) (K := ↥K)
    T ell.toLinearMap C₀ hbd
  have hAann : ∀ p : Nat.Primes, p ∉ S → A (T (feEulerTangentOn D hD p)) = 0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hann p hp
    have hre : (A (T (feEulerTangentOn D hD p))).re = 0 := by
      rw [hA (feEulerTangentOn D hD p)]
      exact h1
    have hTi : T (holoOnImul D (feEulerTangentOn D hD p))
        = Complex.I • T (feEulerTangentOn D hD p) := rfl
    have him : (Complex.I * A (T (feEulerTangentOn D hD p))).re = 0 := by
      have h := hA (holoOnImul D (feEulerTangentOn D hD p))
      rw [hTi, map_smul, smul_eq_mul] at h
      rw [h]
      exact h2
    rw [Complex.mul_re] at him
    simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_eq_zero] at him
    exact Complex.ext hre him
  -- the reflection of the total carrier and the oddified functional
  have hKtotrefl : ∀ z ∈ Ktot, 1 - z ∈ Ktot := by
    rintro z (hz | hz)
    · exact hK'Ktot (hmapKK' z hz)
    · rw [hK'def, mem_reflCarrier] at hz
      exact hKKtot hz
  set tau : C(Ktot, Ktot) :=
    ⟨fun z => ⟨1 - (z : ℂ), hKtotrefl _ z.2⟩,
      Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _⟩ with htau
  set Q : C(Ktot, ℂ) →L[ℂ] C(K, ℂ) :=
    precompCLM (inclMap hKKtot)
      - (precompCLM (feReflMap hmapKK')).comp (precompCLM (inclMap hK'Ktot)) with hQ
  set total : C(Ktot, ℂ) →L[ℂ] ℂ := A.comp Q with htotal
  have hQapply : ∀ (h : C(Ktot, ℂ)) (z : K),
      Q h z = h ⟨(z : ℂ), hKKtot z.2⟩ - h ⟨1 - (z : ℂ), hK'Ktot (hmapKK' _ z.2)⟩ := by
    intro h z
    rfl
  -- the total functional annihilates the symmetrised tangents
  have hcoordval : ∀ (p : ℕ), 2 ≤ p → ∀ k : Ktot,
      compactPrimeEulerUnitTangent (coordMap Ktot) p k = eulerTangent p (k : ℂ) := by
    intro p hp k
    rw [compactPrimeEulerUnitTangent_coordMap halpha (fun w hw => hKtotre w hw) hp k]
    rfl
  have htotFE : ∀ p : Nat.Primes, p ∉ S →
      total (compactPrimeEulerUnitFETangent (coordMap Ktot) tau (p : ℕ)) = 0 := by
    intro p hp
    have hval : Q (compactPrimeEulerUnitFETangent (coordMap Ktot) tau (p : ℕ))
        = (2 : ℂ) • T (feEulerTangentOn D hD p) := by
      ext z
      rw [hQapply]
      simp only [compactPrimeEulerUnitFETangent_apply, ContinuousMap.smul_apply, smul_eq_mul]
      rw [hcoordval (p : ℕ) p.2.two_le, hcoordval (p : ℕ) p.2.two_le,
        hcoordval (p : ℕ) p.2.two_le, hcoordval (p : ℕ) p.2.two_le]
      show eulerTangent (p : ℕ) (z : ℂ) - eulerTangent (p : ℕ) (1 - (z : ℂ))
        - (eulerTangent (p : ℕ) (1 - (z : ℂ)) - eulerTangent (p : ℕ) (1 - (1 - (z : ℂ))))
        = 2 * feEulerTangent (p : ℕ) (z : ℂ)
      rw [show (1 : ℂ) - (1 - (z : ℂ)) = (z : ℂ) by ring, feEulerTangent]
      ring
    rw [htotal, ContinuousLinearMap.comp_apply, hval, map_smul, hAann p hp, smul_zero]
  -- the total functional kills every power of the coordinate
  set Bsum : ℝ := ∑ q ∈ S, Real.log ((q : Nat.Primes) : ℝ) with hBsum
  have hBsum0 : 0 ≤ Bsum := by
    rw [hBsum]
    positivity
  set R₀ : ℝ := 1 + Bsum with hR₀def
  have hR₀ : 0 < R₀ := by rw [hR₀def]; linarith
  set Lodd : C(Ktot, ℂ) →L[ℂ] ℂ :=
    total.comp (ContinuousLinearMap.id ℂ C(Ktot, ℂ) - ContinuousMap.compCLM ℂ ℂ tau) with hLodd
  have hLoddann : ∀ p : Nat.Primes, R₀ + 1 < Real.log ((p : ℕ) : ℝ) →
      Lodd (compactPrimeEulerUnitTangent (coordMap Ktot) (p : ℕ)) = 0 := by
    intro p hp
    have hpnot : p ∉ S := by
      intro hpS
      have hlognonneg : ∀ q ∈ S, 0 ≤ Real.log ((q : Nat.Primes) : ℝ) := by
        intro q _
        exact Real.log_nonneg (by exact_mod_cast q.prop.one_lt.le)
      have hle : Real.log ((p : Nat.Primes) : ℝ) ≤ Bsum := by
        rw [hBsum]
        exact Finset.single_le_sum hlognonneg hpS
      rw [hR₀def] at hp
      have hcast : Real.log ((p : ℕ) : ℝ) = Real.log ((p : Nat.Primes) : ℝ) := rfl
      rw [hcast] at hp
      linarith
    have := htotFE p hpnot
    rw [hLodd]
    simpa [compactPrimeEulerUnitFETangent] using this
  have hFodd := compactFourierBorel_eq_zero_of_tangent_annihilation_rightRectangle
    Lodd (coordMap Ktot) alpha M R₀ halpha hR₀
    (fun k => hKtotre (k : ℂ) k.2) (fun k => hMK (k : ℂ) k.2) hLoddann
  have hLoddpow : ∀ N : ℕ, Lodd (coordMap Ktot ^ N) = 0 :=
    fun N => map_coordinate_pow_eq_zero_of_fourierBorel_zero Lodd (coordMap Ktot) hFodd N
  have hQneg : ∀ N : ℕ, Q ((coordMap Ktot ^ N).comp tau) = -Q (coordMap Ktot ^ N) := by
    intro N
    ext z
    rw [hQapply, ContinuousMap.neg_apply, hQapply]
    show ((1 : ℂ) - (z : ℂ)) ^ N - ((1 : ℂ) - (1 - (z : ℂ))) ^ N
      = -((z : ℂ) ^ N - ((1 : ℂ) - (z : ℂ)) ^ N)
    rw [show (1 : ℂ) - (1 - (z : ℂ)) = (z : ℂ) by ring]
    ring
  have htotpow : ∀ N : ℕ, total (coordMap Ktot ^ N) = 0 := by
    intro N
    have hodd := hLoddpow N
    rw [hLodd] at hodd
    have hexp : total (coordMap Ktot ^ N) - total ((coordMap Ktot ^ N).comp tau) = 0 := by
      simpa using hodd
    have hcomp : total ((coordMap Ktot ^ N).comp tau) = -total (coordMap Ktot ^ N) := by
      rw [htotal, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hQneg N, map_neg]
    rw [hcomp] at hexp
    have : (2 : ℂ) * total (coordMap Ktot ^ N) = 0 := by linear_combination hexp
    simpa using this
  -- the transform of the total functional splits
  have hCtot : ∀ v : ℂ, v ∉ Ktot → functionalCauchyTransform total v
      = functionalCauchyTransform A v + functionalCauchyTransform A (1 - v) := by
    intro v hv
    have hvK : v ∉ K := fun hc => hv (hKKtot hc)
    have hvK' : (1 - v) ∉ K := by
      intro hc
      exact hv (hK'Ktot (by rw [hK'def, mem_reflCarrier]; exact hc))
    have hQker : Q (kernelFun Ktot hv) = kernelFun K hvK + kernelFun K hvK' := by
      ext z
      rw [hQapply, ContinuousMap.add_apply, kernelFun_apply, kernelFun_apply, kernelFun_apply]
      show (v - (z : ℂ))⁻¹ - (v - (1 - (z : ℂ)))⁻¹ = (v - (z : ℂ))⁻¹ + (1 - v - (z : ℂ))⁻¹
      rw [show v - (1 - (z : ℂ)) = -(1 - v - (z : ℂ)) by ring, inv_neg]
      ring
    rw [cauchyTransform_eq total hv, cauchyTransform_eq A hvK, cauchyTransform_eq A hvK',
      htotal, ContinuousLinearMap.comp_apply, hQker, map_add]
  -- the transform vanishes on the separating vertical strip
  have hvert : {v : ℂ | 1 - a < v.re ∧ v.re < a} ⊆ Ktotᶜ := by
    intro v hv hcon
    rcases hcon with hcon | hcon
    · exact absurd (haK v hcon) (not_le.mpr hv.2)
    · exact absurd (hK'a v hcon) (not_le.mpr hv.1)
  have hstrip : ∀ v : ℂ, 1 - a < v.re → v.re < a → functionalCauchyTransform total v = 0 := by
    intro v h1 h2
    have hfar : ∀ w : ℂ, 1 + R < ‖w‖ → functionalCauchyTransform total w = 0 := fun w hw =>
      cauchyTransform_eq_zero_of_lt total htotpow (by linarith) hKtotR hw
    have hopenfar : IsOpen {w : ℂ | 1 + R < ‖w‖} := isOpen_lt continuous_const continuous_norm
    set v₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + ((R + 2 : ℝ) : ℂ) * Complex.I with hv₀
    have hv₀re : v₀.re = 1 / 2 := by rw [hv₀]; simp
    have hv₀im : v₀.im = R + 2 := by rw [hv₀]; simp
    have hv₀far : 1 + R < ‖v₀‖ := by
      have h := Complex.abs_im_le_norm v₀
      rw [hv₀im, abs_of_nonneg (by linarith)] at h
      linarith
    have hv₀strip : v₀ ∈ {w : ℂ | 1 - a < w.re ∧ w.re < a} := by
      rw [Set.mem_setOf_eq, hv₀re]
      exact ⟨by linarith, ha⟩
    have hanal : AnalyticOnNhd ℂ (functionalCauchyTransform total)
        {w : ℂ | 1 - a < w.re ∧ w.re < a} :=
      (analyticOnNhd_functionalCauchyTransform hKtotcompact total).mono hvert
    have hpre : IsPreconnected {w : ℂ | 1 - a < w.re ∧ w.re < a} :=
      ((convex_halfSpace_re_gt (1 - a)).inter (convex_halfSpace_re_lt a)).isPreconnected
    have hev : functionalCauchyTransform total =ᶠ[nhds v₀] 0 := by
      filter_upwards [hopenfar.mem_nhds hv₀far] with w hw
      exact hfar w hw
    exact hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hv₀strip hev ⟨h1, h2⟩
  -- gluing across the critical line
  have hCA : ∀ v, v ∉ K → functionalCauchyTransform A v = 0 := by
    refine cauchyTransform_eq_zero_of_glue_re (Kc' := K') hKcompact (c₁ := 1 - a) (c₂ := a)
      (R := 1 + R) (by linarith) haK hK'a
      (fun z hz => le_trans (hRK z hz) (by linarith)) hK'R
      A (-(feReflFunctional hmapKK' A)) ?_
      (isPreconnected_compl_of_convex_compact hKcompact hKconv)
    intro v h1 h2
    have hv : v ∉ Ktot := hvert ⟨h1, h2⟩
    have hvK' : v ∉ K' := fun hc => hv (hK'Ktot hc)
    have hneg : functionalCauchyTransform (-(feReflFunctional hmapKK' A)) v
        = -functionalCauchyTransform (feReflFunctional hmapKK' A) v := rfl
    have hsplit := hCtot v hv
    have hzero := hstrip v h1 h2
    rw [hsplit] at hzero
    rw [hneg, cauchyTransform_feReflFunctional hmapKK' A hvK']
    linear_combination hzero
  -- Cauchy--Pompeiu finishes
  intro y
  obtain ⟨G, hG, hGy⟩ := y.2
  have hTy : ∀ z : K, T y z = G (z : ℂ) := by
    intro z
    rw [hT, holoOnRestrict_apply]
    exact hGy _
  have hLy := apply_eq_zero_of_cauchyTransform_eq_zero_of_isOpen (K := K)
    hKcompact hDopen hKD hG A hCA (T y) hTy
  have hfin := hA y
  rw [hLy] at hfin
  simpa using hfin.symm

/-- The symmetrised tangent family indexed by the retained primes and the two real directions. -/
def feEulerTangentOnFamily (D : Set ℂ) (hD : D ⊆ rightCriticalStrip) (S : Finset Nat.Primes) :
    {p : Nat.Primes // p ∉ S} × Bool → holoOn D :=
  fun q => if q.2 then holoOnImul D (feEulerTangentOn D hD (q.1 : Nat.Primes))
    else feEulerTangentOn D hD (q.1 : Nat.Primes)

/-- **The cofinite symmetrised Euler tangents span a dense subspace of the holomorphic functions on
a convex domain right of the critical line.** -/
theorem topologicalClosure_span_feEulerTangentOn_eq_top
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hD : D ⊆ rightCriticalStrip)
    (S : Finset Nat.Primes) :
    (Submodule.span ℝ (Set.range (feEulerTangentOnFamily D hD S))).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs
    (E := holoOn D) (Submodule.span ℝ (Set.range (feEulerTangentOnFamily D hD S))) ?_
  intro ell hell
  have hann : ∀ p : Nat.Primes, p ∉ S →
      ell (feEulerTangentOn D hD p) = 0 ∧ ell (holoOnImul D (feEulerTangentOn D hD p)) = 0 := by
    intro p hp
    constructor
    · refine hell _ (Submodule.subset_span ⟨(⟨p, hp⟩, false), ?_⟩)
      simp [feEulerTangentOnFamily]
    · refine hell _ (Submodule.subset_span ⟨(⟨p, hp⟩, true), ?_⟩)
      simp [feEulerTangentOnFamily]
  exact ContinuousLinearMap.ext
    (holoOn_eq_zero_of_annihilates_feEulerTangent hDopen hDconv hD S ell hann)


/-- **Global strip form.**  On the whole open strip `1/2 < Re s < 1` the cofinite symmetrised Euler
tangents span a dense subspace of the holomorphic functions. -/
theorem topologicalClosure_span_feEulerTangent_rightCriticalStrip_eq_top (S : Finset Nat.Primes) :
    (Submodule.span ℝ (Set.range
      (feEulerTangentOnFamily rightCriticalStrip (subset_refl _) S))).topologicalClosure = ⊤ :=
  topologicalClosure_span_feEulerTangentOn_eq_top isOpen_rightCriticalStrip
    convex_rightCriticalStrip (subset_refl _) S

end Completeness

end RHTower
