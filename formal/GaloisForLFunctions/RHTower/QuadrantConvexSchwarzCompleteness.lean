import GaloisForLFunctions.RHTower.StripFEEulerCompleteness
import GaloisForLFunctions.HTGeometry.CauchyTransformGluing

/-!
# Schwarz-real completeness of the symmetrised Euler tangents on a convex quadrant domain

On a convex domain inside the open quadrant `1/2 < Re s < 1`, `Im s > 0` the symmetrised tangents
`u_p` are complete for the *real* span: a continuous real functional annihilating a cofinite set of
them is zero.

The functional is the real part of a complex functional carried by a compact convex `K` in the
domain.  Adding its Schwarz reflection produces a functional on `K ∪ conj K` that annihilates the
Schwarz-real tangents outright.  Reflecting that doubled functional in the critical line and
subtracting gives a functional on the four blocks killing every power of the coordinate, so the
vertical gluing kills the doubled transform left of the carrier, and the identity theorem carries
that vanishing along the horizontal strip separating `K` from `conj K`.  The horizontal gluing then
kills the transform of the original functional, and Cauchy–Pompeiu finishes.

* `RHTower.holoOn_eq_zero_of_annihilates_feEulerTangent_real`;
* `RHTower.topologicalClosure_realSpan_feEulerTangentOn_eq_top`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

theorem criticalQuadrant_subset_rightCriticalStrip : criticalQuadrant ⊆ rightCriticalStrip :=
  fun _ hz => ⟨hz.1, hz.2.1⟩

/-- The conjugate of a carrier. -/
def conjCarrier (K : Set ℂ) : Set ℂ := (starRingEnd ℂ) '' K

theorem isCompact_conjCarrier {K : Set ℂ} (hK : IsCompact K) : IsCompact (conjCarrier K) :=
  hK.image Complex.continuous_conj

theorem conj_mem_conjCarrier {K : Set ℂ} {z : ℂ} (hz : z ∈ K) :
    (starRingEnd ℂ) z ∈ conjCarrier K := ⟨z, hz, rfl⟩

theorem conj_mem_of_mem_conjCarrier {K : Set ℂ} {z : ℂ} (hz : z ∈ conjCarrier K) :
    (starRingEnd ℂ) z ∈ K := by
  obtain ⟨w, hw, rfl⟩ := hz
  simpa using hw

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Cofinite real annihilation of the symmetrised Euler tangents kills every continuous real
functional on a convex domain inside the critical quadrant.** -/
theorem holoOn_eq_zero_of_annihilates_feEulerTangent_real
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hDQ : D ⊆ criticalQuadrant)
    (S : Finset Nat.Primes) (ell : holoOn D →L[ℝ] ℝ)
    (hann : ∀ p : Nat.Primes, p ∉ S →
      ell (feEulerTangentOn D (hDQ.trans criticalQuadrant_subset_rightCriticalStrip) p) = 0) :
    ∀ y : holoOn D, ell y = 0 := by
  classical
  set hD : D ⊆ rightCriticalStrip := hDQ.trans criticalQuadrant_subset_rightCriticalStrip with hDdef
  obtain ⟨K₀, C₀, hK₀, hC₀, hbnd⟩ := exists_compact_dual_bound (holoOn D) ell
  set K₁ : Set ℂ := (Subtype.val : ↥D → ℂ) '' K₀ with hK₁def
  have hK₁ : IsCompact K₁ := hK₀.image continuous_subtype_val
  have hK₁D : K₁ ⊆ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨K, hKcompact, hKconv, hK₁K, hKD⟩ :=
    exists_compact_convex_between hK₁ hDopen hDconv hK₁D
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  obtain ⟨a, ha, haK⟩ : ∃ a : ℝ, 1 / 2 < a ∧ ∀ z ∈ K, a ≤ z.re := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨3 / 4, by norm_num, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMinOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => z.re))
      exact ⟨z₀.re, (hDQ (hKD hz₀K)).1, fun z hz => hz₀ hz⟩
  obtain ⟨b, hb, hbK⟩ : ∃ b : ℝ, b < 1 ∧ ∀ z ∈ K, z.re ≤ b := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨3 / 4, by norm_num, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMaxOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => z.re))
      exact ⟨z₀.re, (hDQ (hKD hz₀K)).2.1, fun z hz => hz₀ hz⟩
  obtain ⟨c, hc, hcK⟩ : ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ z.im := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMinOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => z.im))
      exact ⟨z₀.im, (hDQ (hKD hz₀K)).2.2, fun z hz => hz₀ hz⟩
  obtain ⟨R, hRnn, hRK⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ‖z‖ ≤ R := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨0, le_rfl, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMaxOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => ‖z‖))
      exact ⟨‖z₀‖, norm_nonneg _, fun z hz => hz₀ hz⟩
  -- the conjugate block and the doubled carrier
  set Kbar : Set ℂ := conjCarrier K with hKbardef
  have hKbarcompact : IsCompact Kbar := isCompact_conjCarrier hKcompact
  haveI : CompactSpace Kbar := isCompact_iff_compactSpace.mp hKbarcompact
  have hKbarre : ∀ z ∈ Kbar, a ≤ z.re ∧ z.re ≤ b := by
    intro z hz
    have h := conj_mem_of_mem_conjCarrier hz
    have h1 := haK _ h
    have h2 := hbK _ h
    simp only [Complex.conj_re] at h1 h2
    exact ⟨h1, h2⟩
  have hKbarim : ∀ z ∈ Kbar, z.im ≤ -c := by
    intro z hz
    have h := hcK _ (conj_mem_of_mem_conjCarrier hz)
    simp only [Complex.conj_im] at h
    linarith
  have hKbarR : ∀ z ∈ Kbar, ‖z‖ ≤ R := by
    intro z hz
    have h := hRK _ (conj_mem_of_mem_conjCarrier hz)
    rwa [RCLike.norm_conj] at h
  set Kt : Set ℂ := K ∪ Kbar with hKtdef
  have hKtcompact : IsCompact Kt := hKcompact.union hKbarcompact
  haveI : CompactSpace Kt := isCompact_iff_compactSpace.mp hKtcompact
  have hKKt : K ⊆ Kt := Set.subset_union_left
  have hKbarKt : Kbar ⊆ Kt := Set.subset_union_right
  have hconjKt : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt := by
    rintro z (hz | hz)
    · exact hKbarKt (conj_mem_conjCarrier hz)
    · exact hKKt (conj_mem_of_mem_conjCarrier hz)
  have hKtre : ∀ z ∈ Kt, a ≤ z.re ∧ z.re ≤ b := by
    rintro z (hz | hz)
    · exact ⟨haK z hz, hbK z hz⟩
    · exact hKbarre z hz
  have hKtR : ∀ z ∈ Kt, ‖z‖ ≤ R := by
    rintro z (hz | hz)
    · exact hRK z hz
    · exact hKbarR z hz
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
  set doubled : C(Kt, ℂ) →L[ℂ] ℂ := doubledFunctional hKKt hconjKt A with hdoubled
  -- the symmetrised tangent on the doubled carrier
  have hKtstrip : Kt ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    intro z hz
    exact ⟨by linarith [(hKtre z hz).1], by linarith [(hKtre z hz).2]⟩
  have hfecont : ∀ p : Nat.Primes, Continuous fun z : Kt => feEulerTangent (p : ℕ) (z : ℂ) :=
    fun p => ((differentiableOn_feEulerTangent_strip p.2).continuousOn.mono hKtstrip).restrict
  set uKt : Nat.Primes → C(Kt, ℂ) := fun p => ⟨fun z => feEulerTangent (p : ℕ) (z : ℂ),
    hfecont p⟩ with huKt
  have hsigma : ∀ p : Nat.Primes, sigmaMap hconjKt (uKt p) = uKt p := by
    intro p
    ext z
    rw [sigmaMap_apply, huKt]
    show (starRingEnd ℂ) (feEulerTangent (p : ℕ) ((starRingEnd ℂ) (z : ℂ)))
      = feEulerTangent (p : ℕ) (z : ℂ)
    rw [feEulerTangent_conj p.2.pos, Complex.conj_conj]
  have hrestr : ∀ p : Nat.Primes, precompCLM (inclMap hKKt) (uKt p) = T (feEulerTangentOn D hD p) :=
    fun p => rfl
  have hdoubledann : ∀ p : Nat.Primes, p ∉ S → doubled (uKt p) = 0 := by
    intro p hp
    have h : (ell.toLinearMap (feEulerTangentOn D hD p) : ℝ) = 0 := hann p hp
    rw [hdoubled, doubledFunctional_apply_of_sigma_eq hKKt hconjKt A (hsigma p), hrestr p,
      hA (feEulerTangentOn D hD p), h]
    norm_num
  -- reflection in the critical line
  set Kt' : Set ℂ := reflCarrier Kt with hKt'def
  have hKt'compact : IsCompact Kt' := isCompact_reflCarrier hKtcompact
  haveI : CompactSpace Kt' := isCompact_iff_compactSpace.mp hKt'compact
  set Ktot : Set ℂ := Kt ∪ Kt' with hKtotdef
  have hKtotcompact : IsCompact Ktot := hKtcompact.union hKt'compact
  haveI : CompactSpace Ktot := isCompact_iff_compactSpace.mp hKtotcompact
  have hKtKtot : Kt ⊆ Ktot := Set.subset_union_left
  have hKt'Ktot : Kt' ⊆ Ktot := Set.subset_union_right
  have hmapKtKt' : ∀ z ∈ Kt, 1 - z ∈ Kt' := fun z hz => one_sub_mem_reflCarrier hz
  have hKt'a : ∀ z ∈ Kt', z.re ≤ 1 - a := by
    intro z hz
    rw [hKt'def, mem_reflCarrier] at hz
    have h := (hKtre _ hz).1
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have hKt'b : ∀ z ∈ Kt', 1 - b ≤ z.re := by
    intro z hz
    rw [hKt'def, mem_reflCarrier] at hz
    have h := (hKtre _ hz).2
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  have hKt'R : ∀ z ∈ Kt', ‖z‖ ≤ 1 + R := by
    intro z hz
    rw [hKt'def, mem_reflCarrier] at hz
    have h := hKtR _ hz
    have hz' : z = 1 - (1 - z) := by ring
    rw [hz']
    calc ‖1 - (1 - z)‖ ≤ ‖(1 : ℂ)‖ + ‖1 - z‖ := norm_sub_le _ _
      _ ≤ 1 + R := by simpa using h
  set alpha : ℝ := min a (1 - b) with halphadef
  have halpha : 0 < alpha := lt_min (by linarith) (by linarith)
  have hKtotre : ∀ z ∈ Ktot, alpha ≤ z.re := by
    rintro z (hz | hz)
    · exact le_trans (min_le_left _ _) (hKtre z hz).1
    · exact le_trans (min_le_right _ _) (hKt'b z hz)
  have hKtotR : ∀ z ∈ Ktot, ‖z‖ ≤ 1 + R := by
    rintro z (hz | hz)
    · exact le_trans (hKtR z hz) (by linarith)
    · exact hKt'R z hz
  obtain ⟨M, hMK⟩ : ∃ M : ℝ, ∀ z ∈ Ktot, |z.im| ≤ M := by
    rcases Ktot.eq_empty_or_nonempty with hemp | hne
    · exact ⟨0, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKtotcompact.exists_isMaxOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => |z.im|))
      exact ⟨|z₀.im|, fun z hz => hz₀ hz⟩
  have hKtotrefl : ∀ z ∈ Ktot, 1 - z ∈ Ktot := by
    rintro z (hz | hz)
    · exact hKt'Ktot (hmapKtKt' z hz)
    · rw [hKt'def, mem_reflCarrier] at hz
      exact hKtKtot hz
  set tau : C(Ktot, Ktot) :=
    ⟨fun z => ⟨1 - (z : ℂ), hKtotrefl _ z.2⟩,
      Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _⟩ with htau
  set Q : C(Ktot, ℂ) →L[ℂ] C(Kt, ℂ) :=
    precompCLM (inclMap hKtKtot)
      - (precompCLM (feReflMap hmapKtKt')).comp (precompCLM (inclMap hKt'Ktot)) with hQ
  set total : C(Ktot, ℂ) →L[ℂ] ℂ := doubled.comp Q with htotal
  have hQapply : ∀ (h : C(Ktot, ℂ)) (z : Kt),
      Q h z = h ⟨(z : ℂ), hKtKtot z.2⟩ - h ⟨1 - (z : ℂ), hKt'Ktot (hmapKtKt' _ z.2)⟩ := by
    intro h z
    rfl
  have hcoordval : ∀ (p : ℕ), 2 ≤ p → ∀ k : Ktot,
      compactPrimeEulerUnitTangent (coordMap Ktot) p k = eulerTangent p (k : ℂ) := by
    intro p hp k
    rw [compactPrimeEulerUnitTangent_coordMap halpha (fun w hw => hKtotre w hw) hp k]
    rfl
  have htotFE : ∀ p : Nat.Primes, p ∉ S →
      total (compactPrimeEulerUnitFETangent (coordMap Ktot) tau (p : ℕ)) = 0 := by
    intro p hp
    have hval : Q (compactPrimeEulerUnitFETangent (coordMap Ktot) tau (p : ℕ))
        = (2 : ℂ) • uKt p := by
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
    rw [htotal, ContinuousLinearMap.comp_apply, hval, map_smul, hdoubledann p hp, smul_zero]
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
    have h := htotFE p hpnot
    rw [hLodd]
    simpa [compactPrimeEulerUnitFETangent] using h
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
    have h2 : (2 : ℂ) * total (coordMap Ktot ^ N) = 0 := by linear_combination hexp
    simpa using h2
  have hCtot : ∀ v : ℂ, v ∉ Ktot → functionalCauchyTransform total v
      = functionalCauchyTransform doubled v + functionalCauchyTransform doubled (1 - v) := by
    intro v hv
    have hvKt : v ∉ Kt := fun hcon => hv (hKtKtot hcon)
    have hvKt' : (1 - v) ∉ Kt := by
      intro hcon
      exact hv (hKt'Ktot (by rw [hKt'def, mem_reflCarrier]; exact hcon))
    have hQker : Q (kernelFun Ktot hv) = kernelFun Kt hvKt + kernelFun Kt hvKt' := by
      ext z
      rw [hQapply, ContinuousMap.add_apply, kernelFun_apply, kernelFun_apply, kernelFun_apply]
      show (v - (z : ℂ))⁻¹ - (v - (1 - (z : ℂ)))⁻¹ = (v - (z : ℂ))⁻¹ + (1 - v - (z : ℂ))⁻¹
      rw [show v - (1 - (z : ℂ)) = -(1 - v - (z : ℂ)) by ring, inv_neg]
      ring
    rw [cauchyTransform_eq total hv, cauchyTransform_eq doubled hvKt,
      cauchyTransform_eq doubled hvKt', htotal, ContinuousLinearMap.comp_apply, hQker, map_add]
  have hvert : {v : ℂ | 1 - a < v.re ∧ v.re < a} ⊆ Ktotᶜ := by
    intro v hv hcon
    rcases hcon with hcon | hcon
    · exact absurd (hKtre v hcon).1 (not_le.mpr hv.2)
    · exact absurd (hKt'a v hcon) (not_le.mpr hv.1)
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
  -- the doubled transform vanishes left of the carrier
  have hdoubledlow : ∀ v : ℂ, v.re < a → functionalCauchyTransform doubled v = 0 := by
    refine cauchyTransform_eq_zero_of_glue_re_lt (Kc := Kt) (Kc' := Kt') (c₁ := 1 - a) (c₂ := a)
      (R := 1 + R) (by linarith) (fun z hz => (hKtre z hz).1) hKt'a
      (fun z hz => le_trans (hKtR z hz) (by linarith)) hKt'R
      doubled (-(feReflFunctional hmapKtKt' doubled)) ?_
    intro v h1 h2
    have hv : v ∉ Ktot := hvert ⟨h1, h2⟩
    have hvKt' : v ∉ Kt' := fun hcon => hv (hKt'Ktot hcon)
    have hneg : functionalCauchyTransform (-(feReflFunctional hmapKtKt' doubled)) v
        = -functionalCauchyTransform (feReflFunctional hmapKtKt' doubled) v := rfl
    have hsplit := hCtot v hv
    have hzero := hstrip v h1 h2
    rw [hsplit] at hzero
    rw [hneg, cauchyTransform_feReflFunctional hmapKtKt' doubled hvKt']
    linear_combination hzero
  -- and hence on the whole horizontal strip separating the two blocks
  have hmidKt : {v : ℂ | -c < v.im ∧ v.im < c} ⊆ Ktᶜ := by
    intro v hv hcon
    rcases hcon with hcon | hcon
    · exact absurd (hcK v hcon) (not_le.mpr hv.2)
    · exact absurd (hKbarim v hcon) (not_le.mpr hv.1)
  have hdoubledmid : ∀ v : ℂ, -c < v.im → v.im < c → functionalCauchyTransform doubled v = 0 := by
    intro v h1 h2
    set w₀ : ℂ := ((a - 1 : ℝ) : ℂ) with hw₀
    have hw₀re : w₀.re = a - 1 := by rw [hw₀]; simp
    have hw₀im : w₀.im = 0 := by rw [hw₀]; simp
    have hw₀mid : w₀ ∈ {v : ℂ | -c < v.im ∧ v.im < c} := by
      rw [Set.mem_setOf_eq, hw₀im]
      exact ⟨by linarith, hc⟩
    have hopenlow : IsOpen {w : ℂ | w.re < a} := isOpen_lt Complex.continuous_re continuous_const
    have hanal : AnalyticOnNhd ℂ (functionalCauchyTransform doubled)
        {v : ℂ | -c < v.im ∧ v.im < c} :=
      (analyticOnNhd_functionalCauchyTransform hKtcompact doubled).mono hmidKt
    have hpre : IsPreconnected {v : ℂ | -c < v.im ∧ v.im < c} :=
      ((convex_halfSpace_im_gt (-c)).inter (convex_halfSpace_im_lt c)).isPreconnected
    have hev : functionalCauchyTransform doubled =ᶠ[nhds w₀] 0 := by
      filter_upwards [hopenlow.mem_nhds (show w₀ ∈ {w : ℂ | w.re < a} by
        rw [Set.mem_setOf_eq, hw₀re]; linarith)] with w hw
      exact hdoubledlow w hw
    exact hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hw₀mid hev ⟨h1, h2⟩
  -- the horizontal gluing kills the carrier transform
  have hCA : ∀ v, v ∉ K → functionalCauchyTransform A v = 0 := by
    refine cauchyTransform_eq_zero_of_glue (Kc := K) (Kc' := Kbar) hKcompact (c := c) (R := R) hc
      hcK hKbarim hRK hKbarR A (conjFunctional (fun _ hz => conj_mem_conjCarrier hz) A) ?_
      (isPreconnected_compl_of_convex_compact hKcompact hKconv)
    intro v h1 h2
    have hvKt : v ∉ Kt := hmidKt ⟨h1, h2⟩
    have hvKbar : v ∉ Kbar := fun hcon => hvKt (hKbarKt hcon)
    have hd := cauchyTransform_doubledFunctional hKKt hconjKt A hvKt
    have hcj := cauchyTransform_conjFunctional (K₁ := Kbar) (K₂ := K)
      (fun _ hz => conj_mem_conjCarrier hz) A hvKbar
    have hzero := hdoubledmid v h1 h2
    rw [hdoubled, hd] at hzero
    rw [hcj]
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

/-- **The cofinite symmetrised Euler tangents have dense real span in the holomorphic functions of
any convex domain inside the critical quadrant.** -/
theorem topologicalClosure_realSpan_feEulerTangentOn_eq_top
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hDQ : D ⊆ criticalQuadrant)
    (S : Finset Nat.Primes) :
    (Submodule.span ℝ (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
      feEulerTangentOn D (hDQ.trans criticalQuadrant_subset_rightCriticalStrip)
        (p : Nat.Primes))).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs
    (E := holoOn D) (Submodule.span ℝ (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
      feEulerTangentOn D (hDQ.trans criticalQuadrant_subset_rightCriticalStrip)
        (p : Nat.Primes))) ?_
  intro ell hell
  refine ContinuousLinearMap.ext
    (holoOn_eq_zero_of_annihilates_feEulerTangent_real hDopen hDconv hDQ S ell fun p hp => ?_)
  exact hell _ (Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩)

end RHTower
