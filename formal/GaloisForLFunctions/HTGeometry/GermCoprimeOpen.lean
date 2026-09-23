import GaloisForLFunctions.HTGeometry.GermPreparationAlgebraic
import GaloisForLFunctions.HTGeometry.GermIrreducibleTransfer
import GaloisForLFunctions.HTGeometry.GermFactorial
import GaloisForLFunctions.HTGeometry.GermZeroProjection
import GaloisForLFunctions.HTGeometry.GermSliceNonvanishing
import GaloisForLFunctions.HTGeometry.MonicBezoutConstant
import GaloisForLFunctions.HTGeometry.GermLinearEquiv

/-!
# Coprimality of analytic germs is an open condition

Two holomorphic functions whose germs at a point are relatively prime have relatively prime germs
at every nearby point.

The proof combines the two halves built separately.  In coordinates in which both functions are
regular in the distinguished variable, Weierstrass preparation replaces them by distinguished
polynomials over the ring of parameter germs.  Relative primality of the germs forbids a common
monic factor of positive degree of those polynomials — a monic factor of a distinguished polynomial
is distinguished, so its germ is a non-unit dividing both.  Gauss' lemma then produces a Bézout
identity with a nonzero *parameter* germ on the right:

`p·f + q·g = c ∘ tail`,   `c ≠ 0`.

Now suppose the germs at some nearby point `w` had a common non-unit factor `h`.  Regularity
spreads over the preparation polydisc, so `h` is regular in the same distinguished variable at `w`,
and the zero set of a vanishing regular germ meets every nearby parameter fibre.  Every such zero is
a common zero of `f` and `g`, so `c` vanishes on a whole neighbourhood of the parameter of `w`;
by the identity theorem `c` vanishes identically, contradicting `c ≠ 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric Polynomial

/-! ## Transfer of relative primality -/

/-- **Relative primality transfers along a ring isomorphism.** -/
theorem IsRelPrime.ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {a b : R}
    (h : IsRelPrime a b) : IsRelPrime (e a) (e b) := by
  intro z hza hzb
  have h1 : e.symm z ∣ a := by
    obtain ⟨w, hw⟩ := hza
    refine ⟨e.symm w, ?_⟩
    rw [← map_mul, ← hw, e.symm_apply_apply]
  have h2 : e.symm z ∣ b := by
    obtain ⟨w, hw⟩ := hzb
    refine ⟨e.symm w, ?_⟩
    rw [← map_mul, ← hw, e.symm_apply_apply]
  have h3 : IsUnit (e (e.symm z)) := (h h1 h2).map (e : R →+* S)
  rwa [e.apply_symm_apply] at h3

variable {n : ℕ}

/-- The germ of a sum is the sum of the germs. -/
theorem analyticGermOf_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E}
    {f g : E → ℂ} (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) :
    analyticGermOf (hf.add hg) = analyticGermOf hf + analyticGermOf hg := by
  refine Subtype.ext ?_
  rw [analyticGermOf_val, Subring.coe_add, analyticGermOf_val, analyticGermOf_val]
  rfl

theorem norm_tail_le (w : Fin (n + 1) → ℂ) : ‖(Fin.tail w : Fin n → ℂ)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun i => ?_
  exact norm_le_pi_norm w i.succ

theorem tail_zero' : (Fin.tail (0 : Fin (n + 1) → ℂ) : Fin n → ℂ) = 0 := by
  funext i
  simp [Fin.tail]

/-! ## The regular case -/

/-- **Coprimality propagates, in coordinates where both germs are regular.** -/
theorem eventually_isRelPrime_germ_of_regular {f g : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) (hg : AnalyticAt ℂ g (0 : Fin (n + 1) → ℂ))
    (hfreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0)
    (hgreg : ¬ (fun z : ℂ => g (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0)
    (hrp : IsRelPrime (analyticGermOf hf) (analyticGermOf hg)) :
    ∀ᶠ q in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ (hfq : AnalyticAt ℂ f q) (hgq : AnalyticAt ℂ g q),
      IsRelPrime (analyticGermOf hfq) (analyticGermOf hgq) := by
  classical
  -- Weierstrass preparation of both germs
  obtain ⟨df, α, uf, hufU, hαzero, hfeq⟩ := germ_preparation_algebraic hf hfreg
  obtain ⟨dg, β, ug, hugU, hβzero, hgeq⟩ := germ_preparation_algebraic hg hgreg
  rw [← germEval_distPoly] at hfeq hgeq
  -- no common monic factor of positive degree
  have hno : ∀ D : Polynomial (AnalyticGerm (0 : Fin n → ℂ)), D.Monic → 0 < D.natDegree →
      D ∣ distPoly df α → ¬ D ∣ distPoly dg β := by
    intro D hDM hDdeg hDf hDg
    obtain ⟨Qf, hQf⟩ := hDf
    obtain ⟨Qg, hQg⟩ := hDg
    have hQfM : Qf.Monic := by
      have h1 : D.leadingCoeff * Qf.leadingCoeff = 1 := by
        rw [← Polynomial.leadingCoeff_mul, ← hQf]
        exact distPoly_monic df α
      rwa [hDM.leadingCoeff, one_mul] at h1
    have hDdist : ∀ j, j < D.natDegree → germValueMap n (D.coeff j) = 0 :=
      coeff_eq_zero_of_monic_mul_eq_distPoly hDM hQfM hαzero hQf.symm
    have hDeq : D = distPoly D.natDegree (fun j => D.coeff j) := monic_eq_distPoly hDM
    have hDnu : ¬ IsUnit (germEval n D) := by
      rw [hDeq]
      exact not_isUnit_germEval_distPoly hDdeg hDdist
    have hdvdf : germEval n D ∣ analyticGermOf hf := by
      rw [hfeq]
      exact Dvd.dvd.mul_right (map_dvd (germEval n) ⟨Qf, hQf⟩) uf
    have hdvdg : germEval n D ∣ analyticGermOf hg := by
      rw [hgeq]
      exact Dvd.dvd.mul_right (map_dvd (germEval n) ⟨Qg, hQg⟩) ug
    exact hDnu (hrp hdvdf hdvdg)
  -- the Bézout constant
  obtain ⟨A₀, B₀, c, hc0, hbez⟩ :=
    exists_bezout_const (distPoly_monic df α) (distPoly_monic dg β) hno
  obtain ⟨Uf, hUf⟩ := hufU
  obtain ⟨Ug, hUg⟩ := hugU
  set ufi : AnalyticGerm (0 : Fin (n + 1) → ℂ) :=
    ((Uf⁻¹ : (AnalyticGerm (0 : Fin (n + 1) → ℂ))ˣ) :
      AnalyticGerm (0 : Fin (n + 1) → ℂ)) with hufi
  set ugi : AnalyticGerm (0 : Fin (n + 1) → ℂ) :=
    ((Ug⁻¹ : (AnalyticGerm (0 : Fin (n + 1) → ℂ))ˣ) :
      AnalyticGerm (0 : Fin (n + 1) → ℂ)) with hugi
  have hufmul : uf * ufi = 1 := by
    rw [hufi, ← hUf]
    exact Uf.mul_inv
  have hugmul : ug * ugi = 1 := by
    rw [hugi, ← hUg]
    exact Ug.mul_inv
  have hfinv : germEval n (distPoly df α) = analyticGermOf hf * ufi := by
    rw [hfeq, mul_assoc, hufmul, mul_one]
  have hginv : germEval n (distPoly dg β) = analyticGermOf hg * ugi := by
    rw [hgeq, mul_assoc, hugmul, mul_one]
  have hgermbez :
      (germEval n A₀ * ufi) * analyticGermOf hf + (germEval n B₀ * ugi) * analyticGermOf hg
        = germTail n c := by
    have h := congrArg (germEval n) hbez
    rw [map_add, map_mul, map_mul, hfinv, hginv, germEval_C] at h
    rw [← h]
    ring
  -- analytic representatives
  obtain ⟨p, hpA, hp⟩ := (germEval n A₀ * ufi).2
  obtain ⟨q, hqA, hq⟩ := (germEval n B₀ * ugi).2
  obtain ⟨crep, hcA, hcrep⟩ := c.2
  have hpeq : germEval n A₀ * ufi = analyticGermOf hpA := Subtype.ext hp.symm
  have hqeq : germEval n B₀ * ugi = analyticGermOf hqA := Subtype.ext hq.symm
  have hceq : c = analyticGermOf hcA := Subtype.ext hcrep.symm
  have htailA : AnalyticAt ℂ (fun w : Fin (n + 1) → ℂ => crep (Fin.tail w))
      (0 : Fin (n + 1) → ℂ) := by
    have h := AnalyticAt.comp (g := crep) (f := fun w : Fin (n + 1) → ℂ => (Fin.tail w : Fin n → ℂ))
      (by rw [tail_zero']; exact hcA) analyticAt_tail_analyticGermUnit
    exact h
  have htaileq : germTail n c = analyticGermOf htailA := by
    refine Subtype.ext ?_
    rw [hceq, germTail_analyticGermOf hcA, analyticGermOf_val]
    rfl
  -- the Bézout identity as an identity of functions near the origin
  have hbezfun : (fun w : Fin (n + 1) → ℂ => p w * f w + q w * g w) =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)]
      fun w => crep (Fin.tail w) := by
    refine (analyticGermOf_eq_iff ((hpA.mul hf).add (hqA.mul hg)) htailA).mp ?_
    rw [analyticGermOf_add (hpA.mul hf) (hqA.mul hg), analyticGermOf_mul hpA hf,
      analyticGermOf_mul hqA hg, ← hpeq, ← hqeq, ← htaileq]
    exact hgermbez
  -- the constant is not identically zero
  have hcne : ¬ crep =ᶠ[𝓝 (0 : Fin n → ℂ)] 0 := by
    intro hcon
    refine hc0 ?_
    rw [hceq]
    refine Subtype.ext ?_
    rw [analyticGermOf_val, ZeroMemClass.coe_zero]
    exact Germ.coe_eq.mpr hcon
  obtain ⟨ρc, hρc, hcrepA⟩ := exists_ball_analyticOnNhd hcA
  -- regularity spreads over a polydisc
  obtain ⟨t, δ, htpos, hδpos, hslice⟩ := exists_polydisc_slice_ne_zero hf hfreg
  obtain ⟨ρ₀, hρ₀, hρ₀spec⟩ := Metric.eventually_nhds_iff.mp hbezfun
  set ρ : ℝ := min (min ρ₀ ρc) (min t δ) with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min hρ₀ hρc) (lt_min htpos hδpos)
  filter_upwards [Metric.ball_mem_nhds (0 : Fin (n + 1) → ℂ) hρpos] with w₀ hw₀
  intro hfq hgq
  -- the basic size estimates at `w₀`
  have hw₀norm : ‖w₀‖ < ρ := by simpa [mem_ball_zero_iff] using hw₀
  have hw₀t : ‖w₀ 0‖ < t :=
    lt_of_le_of_lt (norm_le_pi_norm w₀ 0)
      (lt_of_lt_of_le hw₀norm (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hw₀δ : ‖(Fin.tail w₀ : Fin n → ℂ)‖ < δ :=
    lt_of_le_of_lt (norm_tail_le w₀)
      (lt_of_lt_of_le hw₀norm (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hw₀ρc : ‖(Fin.tail w₀ : Fin n → ℂ)‖ < ρc :=
    lt_of_le_of_lt (norm_tail_le w₀)
      (lt_of_lt_of_le hw₀norm (le_trans (min_le_left _ _) (min_le_right _ _)))
  -- suppose the germs at `w₀` had a common non-unit factor
  by_contra hcon
  obtain ⟨h, hhf, hhg, hhnu⟩ :
      ∃ h : AnalyticGerm w₀, h ∣ analyticGermOf hfq ∧ h ∣ analyticGermOf hgq ∧ ¬ IsUnit h := by
    by_contra hc
    push Not at hc
    exact hcon fun z hz1 hz2 => hc z hz1 hz2
  obtain ⟨hrep, hhA, hheq⟩ := h.2
  have hheq' : h = analyticGermOf hhA := Subtype.ext hheq.symm
  have hhzero : hrep w₀ = 0 := by
    by_contra hne
    refine hhnu ?_
    rw [hheq', isUnit_analyticGerm_iff, analyticGermValue_of hhA]
    exact hne
  -- the two divisibility relations, as identities of functions near `w₀`
  obtain ⟨kf, hkf⟩ := hhf
  obtain ⟨kg, hkg⟩ := hhg
  obtain ⟨kfrep, hkfA, hkfeq⟩ := kf.2
  obtain ⟨kgrep, hkgA, hkgeq⟩ := kg.2
  have hfprod : f =ᶠ[𝓝 w₀] fun w => hrep w * kfrep w := by
    refine (analyticGermOf_eq_iff hfq (hhA.mul hkfA)).mp ?_
    rw [analyticGermOf_mul hhA hkfA, ← hheq',
      ← (Subtype.ext hkfeq.symm : kf = analyticGermOf hkfA)]
    exact hkf
  have hgprod : g =ᶠ[𝓝 w₀] fun w => hrep w * kgrep w := by
    refine (analyticGermOf_eq_iff hgq (hhA.mul hkgA)).mp ?_
    rw [analyticGermOf_mul hhA hkgA, ← hheq',
      ← (Subtype.ext hkgeq.symm : kg = analyticGermOf hkgA)]
    exact hkg
  -- `h` is regular in the distinguished coordinate at `w₀`
  have hhreg : ¬ (fun z : ℂ => hrep (Fin.cons z (Fin.tail w₀))) =ᶠ[𝓝 (w₀ 0)] 0 := by
    intro hzero
    refine hslice (Fin.tail w₀) hw₀δ (w₀ 0) hw₀t ?_
    have hcons : Filter.Tendsto (fun z : ℂ => (Fin.cons z (Fin.tail w₀) : Fin (n + 1) → ℂ))
        (𝓝 (w₀ 0)) (𝓝 w₀) := by
      have hc : Continuous fun z : ℂ => (Fin.cons z (Fin.tail w₀) : Fin (n + 1) → ℂ) := by
        refine continuous_pi fun i => ?_
        induction i using Fin.cases with
        | zero => simpa using continuous_id'
        | succ j => simpa using continuous_const
      have hct : Filter.Tendsto (fun z : ℂ => (Fin.cons z (Fin.tail w₀) : Fin (n + 1) → ℂ))
          (𝓝 (w₀ 0)) (𝓝 (Fin.cons (w₀ 0) (Fin.tail w₀) : Fin (n + 1) → ℂ)) := hc.continuousAt
      rwa [Fin.cons_self_tail] at hct
    filter_upwards [hcons.eventually hfprod, hzero] with z hz1 hz2
    have hz2' : hrep (Fin.cons z (Fin.tail w₀)) = 0 := hz2
    show f (Fin.cons z (Fin.tail w₀)) = 0
    rw [hz1]
    show hrep (Fin.cons z (Fin.tail w₀)) * kfrep (Fin.cons z (Fin.tail w₀)) = 0
    rw [hz2', zero_mul]
  -- the common zero set of `f` and `g` meets every nearby parameter fibre
  set W : Set (Fin (n + 1) → ℂ) :=
    {w | ‖w‖ < ρ} ∩ ({w | f w = hrep w * kfrep w} ∩ {w | g w = hrep w * kgrep w}) with hW
  have hWmem : W ∈ 𝓝 w₀ := by
    refine Filter.inter_mem ?_ (Filter.inter_mem hfprod hgprod)
    have hset : {w : Fin (n + 1) → ℂ | ‖w‖ < ρ} = Metric.ball (0 : Fin (n + 1) → ℂ) ρ := by
      ext w
      simp
    rw [hset]
    exact Metric.isOpen_ball.mem_nhds hw₀
  have hproj := eventually_exists_slice_zero hhA hhzero hhreg hWmem
  -- hence the Bézout constant vanishes near the parameter of `w₀`
  have hcvanish : crep =ᶠ[𝓝 (Fin.tail w₀)] 0 := by
    filter_upwards [hproj] with y hy
    obtain ⟨z, hzW, hzzero⟩ := hy
    obtain ⟨hzρ, hzf, hzg⟩ := hzW
    have hfz : f (Fin.cons z y) = 0 := by
      rw [hzf, hzzero, zero_mul]
    have hgz : g (Fin.cons z y) = 0 := by
      rw [hzg, hzzero, zero_mul]
    have hbz := hρ₀spec (show dist (Fin.cons z y : Fin (n + 1) → ℂ) 0 < ρ₀ from by
      have : ‖(Fin.cons z y : Fin (n + 1) → ℂ)‖ < ρ := hzρ
      rw [dist_zero_right]
      exact lt_of_lt_of_le this (le_trans (min_le_left _ _) (min_le_left _ _)))
    show crep y = 0
    have hbz' : p (Fin.cons z y) * f (Fin.cons z y) + q (Fin.cons z y) * g (Fin.cons z y)
        = crep (Fin.tail (Fin.cons z y : Fin (n + 1) → ℂ)) := hbz
    rw [hfz, hgz, mul_zero, mul_zero, add_zero, Fin.tail_cons] at hbz'
    exact hbz'.symm
  -- the identity theorem kills the constant
  refine hcne ?_
  have hball : IsPreconnected (ball (0 : Fin n → ℂ) ρc) :=
    (convex_ball (0 : Fin n → ℂ) ρc).isPreconnected
  have heqOn := hcrepA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hball
    (show (Fin.tail w₀ : Fin n → ℂ) ∈ ball (0 : Fin n → ℂ) ρc from by
      simpa [mem_ball_zero_iff] using hw₀ρc) hcvanish
  filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) hρc] with y hy
  exact heqOn hy


/-! ## Removing the coordinate hypotheses -/

/-- **Relative primality of germs is invariant under an analytic change of coordinates.** -/
theorem isRelPrime_analyticGermOf_pullback_iff {E E' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {Φ : E → E'} {Ψ : E' → E} {a : E} {b : E'}
    (hΦ : AnalyticAt ℂ Φ a) (hΨ : AnalyticAt ℂ Ψ b) (hab : Φ a = b) (hba : Ψ b = a)
    (h1 : (Ψ ∘ Φ) =ᶠ[𝓝 a] id) (h2 : (Φ ∘ Ψ) =ᶠ[𝓝 b] id)
    {f g : E' → ℂ} (hf : AnalyticAt ℂ f b) (hg : AnalyticAt ℂ g b)
    (hfΦ : AnalyticAt ℂ (f ∘ Φ) a) (hgΦ : AnalyticAt ℂ (g ∘ Φ) a) :
    IsRelPrime (analyticGermOf hfΦ) (analyticGermOf hgΦ)
      ↔ IsRelPrime (analyticGermOf hf) (analyticGermOf hg) := by
  set e := analyticGermEquiv hΦ hΨ hab hba h1 h2 with he
  have hef : e (analyticGermOf hf) = analyticGermOf hfΦ := by
    refine Subtype.ext ?_
    rw [he, analyticGermEquiv_apply, analyticGermPullback_analyticGermOf hΦ hab hf,
      analyticGermOf_val]
  have heg : e (analyticGermOf hg) = analyticGermOf hgΦ := by
    refine Subtype.ext ?_
    rw [he, analyticGermEquiv_apply, analyticGermPullback_analyticGermOf hΦ hab hg,
      analyticGermOf_val]
  constructor
  · intro h
    have hsym := IsRelPrime.ringEquiv e.symm h
    rwa [← hef, ← heg, e.symm_apply_apply, e.symm_apply_apply] at hsym
  · intro h
    have hfwd := IsRelPrime.ringEquiv e h
    rwa [hef, heg] at hfwd

/-- A germ that vanishes identically near the point is the zero germ. -/
theorem analyticGermOf_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E}
    {f : E → ℂ} (hf : AnalyticAt ℂ f p) (h : f =ᶠ[𝓝 p] 0) : analyticGermOf hf = 0 := by
  refine Subtype.ext ?_
  rw [analyticGermOf_val, ZeroMemClass.coe_zero]
  exact Germ.coe_eq.mpr h

/-- **Coprimality of analytic germs is an open condition, at the origin.** -/
theorem eventually_isRelPrime_germ_zero {f g : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) (hg : AnalyticAt ℂ g (0 : Fin (n + 1) → ℂ))
    (hrp : IsRelPrime (analyticGermOf hf) (analyticGermOf hg)) :
    ∀ᶠ q in 𝓝 (0 : Fin (n + 1) → ℂ), ∀ (hfq : AnalyticAt ℂ f q) (hgq : AnalyticAt ℂ g q),
      IsRelPrime (analyticGermOf hfq) (analyticGermOf hgq) := by
  classical
  -- if one of the two germs vanishes identically, the other is a unit and stays one
  by_cases hfz : f =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] 0
  · have hgu : IsUnit (analyticGermOf hg) := by
      have h0 : analyticGermOf hf = 0 := analyticGermOf_eq_zero hf hfz
      rw [h0] at hrp
      exact hrp (dvd_zero _) dvd_rfl
    have hgne : g (0 : Fin (n + 1) → ℂ) ≠ 0 := by
      rw [isUnit_analyticGerm_iff, analyticGermValue_of hg] at hgu
      exact hgu
    filter_upwards [hg.continuousAt.eventually_ne hgne] with q hq hfq hgq
    refine IsRelPrime.symm (IsUnit.isRelPrime_left ?_)
    rw [isUnit_analyticGerm_iff, analyticGermValue_of hgq]
    exact hq
  by_cases hgz : g =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] 0
  · have hfu : IsUnit (analyticGermOf hf) := by
      have h0 : analyticGermOf hg = 0 := analyticGermOf_eq_zero hg hgz
      rw [h0] at hrp
      exact hrp dvd_rfl (dvd_zero _)
    have hfne : f (0 : Fin (n + 1) → ℂ) ≠ 0 := by
      rw [isUnit_analyticGerm_iff, analyticGermValue_of hf] at hfu
      exact hfu
    filter_upwards [hf.continuousAt.eventually_ne hfne] with q hq hfq hgq
    refine IsUnit.isRelPrime_left ?_
    rw [isUnit_analyticGerm_iff, analyticGermValue_of hfq]
    exact hq
  -- otherwise choose coordinates in which both germs are regular
  have hprod : ¬ (fun w : Fin (n + 1) → ℂ => f w * g w) =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] 0 := by
    intro hcon
    exact hgz (eventuallyEq_zero_of_mul_eventuallyEq_zero hf hg hfz hcon)
  obtain ⟨L, hL⟩ := exists_regular_coordinate_change (hf.mul hg) hprod
  have hLmap : ∀ w : Fin (n + 1) → ℂ, AnalyticAt ℂ (fun v : Fin (n + 1) → ℂ => L v) w :=
    fun w => analyticAt_linearMap (L : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) w
  have hLsymm : ∀ w : Fin (n + 1) → ℂ, AnalyticAt ℂ (fun v : Fin (n + 1) → ℂ => L.symm v) w :=
    fun w => analyticAt_linearMap (L.symm : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) w
  have hfL : ∀ w : Fin (n + 1) → ℂ, AnalyticAt ℂ f (L w) → AnalyticAt ℂ (f ∘ ⇑L) w :=
    fun w hw => hw.comp (hLmap w)
  have hgL : ∀ w : Fin (n + 1) → ℂ, AnalyticAt ℂ g (L w) → AnalyticAt ℂ (g ∘ ⇑L) w :=
    fun w hw => hw.comp (hLmap w)
  have hf0 : AnalyticAt ℂ f (L (0 : Fin (n + 1) → ℂ)) := by rw [map_zero]; exact hf
  have hg0 : AnalyticAt ℂ g (L (0 : Fin (n + 1) → ℂ)) := by rw [map_zero]; exact hg
  -- both composed germs are regular in the distinguished coordinate
  have hfreg : ¬ (fun z : ℂ => (f ∘ ⇑L) (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    intro hcon
    refine hL ?_
    filter_upwards [hcon] with z hz
    show f (L (Fin.cons z (0 : Fin n → ℂ))) * g (L (Fin.cons z (0 : Fin n → ℂ))) = 0
    have hz' : f (L (Fin.cons z (0 : Fin n → ℂ))) = 0 := hz
    rw [hz', zero_mul]
  have hgreg : ¬ (fun z : ℂ => (g ∘ ⇑L) (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
    intro hcon
    refine hL ?_
    filter_upwards [hcon] with z hz
    show f (L (Fin.cons z (0 : Fin n → ℂ))) * g (L (Fin.cons z (0 : Fin n → ℂ))) = 0
    have hz' : g (L (Fin.cons z (0 : Fin n → ℂ))) = 0 := hz
    rw [hz', mul_zero]
  -- transport the hypothesis into the new coordinates
  have hrp' : IsRelPrime (analyticGermOf (hfL 0 hf0)) (analyticGermOf (hgL 0 hg0)) := by
    have hequiv := IsRelPrime.ringEquiv (germLinearEquiv L) hrp
    have h1 : germLinearEquiv L (analyticGermOf hf) = analyticGermOf (hfL 0 hf0) := by
      refine Subtype.ext ?_
      rw [germLinearEquiv_analyticGermOf L hf, analyticGermOf_val]
    have h2 : germLinearEquiv L (analyticGermOf hg) = analyticGermOf (hgL 0 hg0) := by
      refine Subtype.ext ?_
      rw [germLinearEquiv_analyticGermOf L hg, analyticGermOf_val]
    rwa [h1, h2] at hequiv
  have hmain := eventually_isRelPrime_germ_of_regular (hfL 0 hf0) (hgL 0 hg0) hfreg hgreg hrp'
  -- and transport the conclusion back
  have htend : Filter.Tendsto (fun w : Fin (n + 1) → ℂ => (L.symm w : Fin (n + 1) → ℂ))
      (𝓝 (0 : Fin (n + 1) → ℂ)) (𝓝 (0 : Fin (n + 1) → ℂ)) := by
    have h1 : Filter.Tendsto (fun w : Fin (n + 1) → ℂ => (L.symm w : Fin (n + 1) → ℂ))
        (𝓝 (0 : Fin (n + 1) → ℂ)) (𝓝 (L.symm (0 : Fin (n + 1) → ℂ))) :=
      (hLsymm 0).continuousAt
    rwa [map_zero] at h1
  filter_upwards [htend.eventually hmain] with q hq hfq hgq
  have hLq : L (L.symm q) = q := L.apply_symm_apply q
  have hfq' : AnalyticAt ℂ f (L (L.symm q)) := by rw [hLq]; exact hfq
  have hgq' : AnalyticAt ℂ g (L (L.symm q)) := by rw [hLq]; exact hgq
  refine (isRelPrime_analyticGermOf_pullback_iff (Φ := ⇑L) (Ψ := ⇑L.symm)
    (hLmap (L.symm q)) (hLsymm q) hLq rfl
    (Filter.Eventually.of_forall fun w => L.symm_apply_apply w)
    (Filter.Eventually.of_forall fun w => L.apply_symm_apply w)
    hfq hgq (hfL _ hfq') (hgL _ hgq')).mp ?_
  exact hq (hfL _ hfq') (hgL _ hgq')

/-- **Coprimality of analytic germs is an open condition.**  If the germs of two holomorphic
functions at a point of `ℂ^{n+1}` are relatively prime, then so are their germs at every point of a
neighbourhood. -/
theorem eventually_isRelPrime_germ {f g : (Fin (n + 1) → ℂ) → ℂ} {p : Fin (n + 1) → ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hrp : IsRelPrime (analyticGermOf hf) (analyticGermOf hg)) :
    ∀ᶠ q in 𝓝 p, ∀ (hfq : AnalyticAt ℂ f q) (hgq : AnalyticAt ℂ g q),
      IsRelPrime (analyticGermOf hfq) (analyticGermOf hgq) := by
  classical
  have hΦ : ∀ w : Fin (n + 1) → ℂ, AnalyticAt ℂ (fun v : Fin (n + 1) → ℂ => v + p) w := by
    intro w
    have h := (analyticAt_id (𝕜 := ℂ) (z := w)).add (analyticAt_const (v := p))
    rw [Pi.add_def] at h
    exact h
  have hΨ : ∀ w : Fin (n + 1) → ℂ, AnalyticAt ℂ (fun v : Fin (n + 1) → ℂ => v - p) w := by
    intro w
    have h := (analyticAt_id (𝕜 := ℂ) (z := w)).sub (analyticAt_const (v := p))
    rw [Pi.sub_def] at h
    exact h
  have hcomp : ∀ (u : (Fin (n + 1) → ℂ) → ℂ) (w : Fin (n + 1) → ℂ),
      AnalyticAt ℂ u (w + p) → AnalyticAt ℂ (u ∘ fun v : Fin (n + 1) → ℂ => v + p) w :=
    fun u w hu => AnalyticAt.comp (g := u) (f := fun v : Fin (n + 1) → ℂ => v + p) hu (hΦ w)
  have hΨΦ : ((fun v : Fin (n + 1) → ℂ => v - p) ∘ fun v : Fin (n + 1) → ℂ => v + p)
      =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] id :=
    Filter.Eventually.of_forall fun w => by simp
  have hΦΨ : ((fun v : Fin (n + 1) → ℂ => v + p) ∘ fun v : Fin (n + 1) → ℂ => v - p)
      =ᶠ[𝓝 p] id :=
    Filter.Eventually.of_forall fun w => by simp
  have hf0 : AnalyticAt ℂ f ((0 : Fin (n + 1) → ℂ) + p) := by rw [zero_add]; exact hf
  have hg0 : AnalyticAt ℂ g ((0 : Fin (n + 1) → ℂ) + p) := by rw [zero_add]; exact hg
  have hrp0 : IsRelPrime (analyticGermOf (hcomp f 0 hf0)) (analyticGermOf (hcomp g 0 hg0)) :=
    (isRelPrime_analyticGermOf_pullback_iff (hΦ 0) (hΨ p) (zero_add p) (sub_self p)
      hΨΦ hΦΨ hf hg (hcomp f 0 hf0) (hcomp g 0 hg0)).mpr hrp
  have hmain := eventually_isRelPrime_germ_zero (hcomp f 0 hf0) (hcomp g 0 hg0) hrp0
  have htend : Filter.Tendsto (fun w : Fin (n + 1) → ℂ => w - p) (𝓝 p)
      (𝓝 (0 : Fin (n + 1) → ℂ)) := by
    have h1 : Filter.Tendsto (fun w : Fin (n + 1) → ℂ => w - p) (𝓝 p) (𝓝 (p - p)) :=
      (hΨ p).continuousAt
    rwa [sub_self] at h1
  filter_upwards [htend.eventually hmain] with q hq hfq hgq
  have hqp : q - p + p = q := by simp
  have hfq' : AnalyticAt ℂ f (q - p + p) := by rw [hqp]; exact hfq
  have hgq' : AnalyticAt ℂ g (q - p + p) := by rw [hqp]; exact hgq
  refine (isRelPrime_analyticGermOf_pullback_iff (hΦ (q - p)) (hΨ q) hqp rfl
    (Filter.Eventually.of_forall fun w => by simp)
    (Filter.Eventually.of_forall fun w => by simp)
    hfq hgq (hcomp f (q - p) hfq') (hcomp g (q - p) hgq')).mp ?_
  exact hq (hcomp f (q - p) hfq') (hcomp g (q - p) hgq')

end GaloisForLFunctions.HTGeometry
