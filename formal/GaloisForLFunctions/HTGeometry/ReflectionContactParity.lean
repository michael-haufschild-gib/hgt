import GaloisForLFunctions.HTGeometry.AnalyticPrimitive
import GaloisForLFunctions.HTGeometry.PositiveContactTropicalization
import GaloisForLFunctions.RHTower.SourceHorizontalWoldProfileResponsePolarization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Reflection-contact parity and minimal oriented rank

A nonzero even positive real-analytic response `I` of order `2k` at `0` (`(RP.1)`) has an analytic
square root `q(t) = tᵏ h(t)` with `h` a positive even analytic unit, unique up to sign
(`(RP.3)`).  An *analytic reflection-oriented realization* of `I` in a real inner-product space `V`
is an orthogonal involution `R` and an analytic curve `Γ` with `Γ(0) = 0`, `Γ(-t) = R Γ(t)`,
`‖Γ'(t)‖² = I(t)` and `Γ(t) ≠ Γ(-t)` for small `t ≠ 0` (`(RP.2)`); `orrank(I)` is the least
dimension of such a realization.

* **Theorem 3.1, `(RP.4)`.**  `orrank(I) = 1` for even `k` and `orrank(I) = 2` for odd `k`.  The
  involution can be neither `+1` (the curve folds) nor `-1` when `k` is odd (then `Γ'` is even, so
  its contact order is even and `‖Γ'‖²` has order divisible by four); in dimension one these are
  the only involutions.  For even `k` the primitive of `q` realizes `I` on the line with `R = -1`;
  for odd `k` the primitive of `q(t)(cos t, sin t)` realizes `I` in the plane with one fixed and one
  reversed direction.
* **Corollary 3.2, `(RP.7a)`.**  For odd `k`, a rank-two realization has `R = diag(1, -1)` in an
  orthonormal eigenbasis; the fixed channel velocity has contact order exactly `k` and the reversed
  channel velocity has even order `> k`.
* **§6.**  The Wold response `cosh u - sinh u / u` has order two, so its oriented rank is two, and
  the sheet swap of the two-sheet packet is exactly the forced involution type: it realizes the Wold
  response.
* **§7.**  An odd analytic ramification of order `r` sends half-order `k` to `r k` and preserves
  the oriented rank.
-/

open Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### Responses and oriented realizations -/

/-- A nonzero even positive real-analytic response of order `2k` at `0`, `(RP.1)`. -/
structure EvenPositiveResponse (I : ℝ → ℝ) (k : ℕ) : Prop where
  analyticAt : AnalyticAt ℝ I 0
  even : ∀ᶠ t in 𝓝 0, I (-t) = I t
  nonneg : ∀ᶠ t in 𝓝 0, 0 ≤ I t
  zero : I 0 = 0
  order : analyticOrderAt I 0 = ((2 * k : ℕ) : ℕ∞)

/-- An analytic reflection-oriented realization of `I` in `V`, `(RP.2)`. -/
structure OrientedRealization (I : ℝ → ℝ) (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] where
  /-- The orthogonal involution. -/
  refl : V ≃ₗᵢ[ℝ] V
  refl_refl : ∀ v, refl (refl v) = v
  /-- The analytic curve. -/
  curve : ℝ → V
  analyticAt : AnalyticAt ℝ curve 0
  curve_zero : curve 0 = 0
  equivariant : ∀ᶠ t in 𝓝 0, curve (-t) = refl (curve t)
  speed : ∀ᶠ t in 𝓝 0, ‖deriv curve t‖ ^ 2 = I t
  separated : ∀ᶠ t in 𝓝[≠] 0, curve t ≠ curve (-t)

/-- `orrank(I)`: the least dimension of an analytic reflection-oriented realization. -/
def orientedRank (I : ℝ → ℝ) : ℕ :=
  sInf {n : ℕ | Nonempty (OrientedRealization I (EuclideanSpace ℝ (Fin n)))}

variable {I : ℝ → ℝ} {k : ℕ}
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem eventually_neg_of_eventually {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝 0, P t) :
    ∀ᶠ t in 𝓝 0, P (-t) := by
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := ℝ)).tendsto (0 : ℝ)
  exact hneg.eventually h

theorem eventually_differentiableAt_of_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} (hf : AnalyticAt ℝ f 0) :
    ∀ᶠ t in 𝓝 0, DifferentiableAt ℝ f t :=
  hf.eventually_analyticAt.mono fun _ ht => ht.differentiableAt

namespace OrientedRealization

/-- **Transport along a linear isometry.** -/
def map [CompleteSpace V] (ρ : OrientedRealization I V) (e : V ≃ₗᵢ[ℝ] W) :
    OrientedRealization I W where
  refl := e.symm.trans (ρ.refl.trans e)
  refl_refl w := by simp [ρ.refl_refl]
  curve t := e (ρ.curve t)
  analyticAt := (e.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp ρ.analyticAt
  curve_zero := by simp [ρ.curve_zero]
  equivariant := by
    filter_upwards [ρ.equivariant] with t ht
    simp [ht]
  speed := by
    filter_upwards [ρ.speed, eventually_differentiableAt_of_analyticAt ρ.analyticAt] with t ht hd
    have hder : HasDerivAt (fun t => e (ρ.curve t)) (e (deriv ρ.curve t)) t :=
      e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
        hd.hasDerivAt
    rw [hder.deriv, LinearIsometryEquiv.norm_map, ht]
  separated := by
    filter_upwards [ρ.separated] with t ht
    exact fun h => ht (e.injective h)

/-- Separation forces a nonzero space. -/
theorem not_subsingleton (ρ : OrientedRealization I V) : ¬ Subsingleton V := by
  intro hV
  obtain ⟨t, ht⟩ := ρ.separated.exists
  exact ht (Subsingleton.elim _ _)

/-- **The involution is not the identity**: it would fold the curve. -/
theorem refl_ne_id (ρ : OrientedRealization I V) : ∃ v, ρ.refl v ≠ v := by
  by_contra h
  push Not at h
  obtain ⟨t, ht1, ht2⟩ := (ρ.separated.and (nhdsWithin_le_nhds ρ.equivariant)).exists
  exact ht1 (by rw [ht2, h])

/-- A realization in a finite-dimensional space gives one in the Euclidean space of the same
dimension. -/
def toEuclidean [FiniteDimensional ℝ V] (ρ : OrientedRealization I V) :
    OrientedRealization I (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
  ρ.map (stdOrthonormalBasis ℝ V).repr

theorem orientedRank_le [FiniteDimensional ℝ V] (ρ : OrientedRealization I V) :
    orientedRank I ≤ Module.finrank ℝ V :=
  Nat.sInf_le ⟨ρ.toEuclidean⟩

theorem finrank_pos [FiniteDimensional ℝ V] (ρ : OrientedRealization I V) :
    0 < Module.finrank ℝ V := by
  rw [Nat.pos_iff_ne_zero, Ne, Module.finrank_zero_iff]
  exact ρ.not_subsingleton

end OrientedRealization

/-! ### Square-root normal form -/

namespace EvenPositiveResponse

theorem order_ne_top (hI : EvenPositiveResponse I k) : analyticOrderAt I 0 ≠ ⊤ := by
  rw [hI.order]
  exact ENat.coe_ne_top _

theorem not_eventually_zero (hI : EvenPositiveResponse I k) : ¬ ∀ᶠ t in 𝓝 0, I t = 0 := by
  rw [← analyticOrderAt_eq_top]
  exact hI.order_ne_top

theorem k_pos (hI : EvenPositiveResponse I k) : 0 < k := by
  obtain ⟨u, hu, hu0, hfactor⟩ := hI.analyticAt.analyticOrderAt_eq_natCast.mp hI.order
  by_contra hk
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
  have h := hfactor.self_of_nhds
  simp [hk0, hI.zero] at h
  exact hu0 h.symm

/-- The contact unit: `I(t) = t^{2k} u(t)` with `u` analytic, even and `u(0) > 0`. -/
theorem exists_unit (hI : EvenPositiveResponse I k) :
    ∃ u : ℝ → ℝ, AnalyticAt ℝ u 0 ∧ 0 < u 0 ∧ (∀ᶠ t in 𝓝 0, u (-t) = u t) ∧
      ∀ᶠ t in 𝓝 0, I t = t ^ (2 * k) * u t := by
  obtain ⟨a, ha⟩ := PositiveAnalyticContact.exists_of_analytic_eventually_nonnegative
    hI.analyticAt hI.order_ne_top hI.nonneg
  rw [hI.order, ENat.toNat_coe] at ha
  obtain ⟨⟨u, hu, hu0, -, hfactor⟩, -, hapos⟩ := ha
  have hfactor' : ∀ᶠ t in 𝓝 0, I t = t ^ (2 * k) * u t := by
    simpa [smul_eq_mul] using hfactor
  refine ⟨u, hu, hu0 ▸ hapos, ?_, hfactor'⟩
  filter_upwards [hfactor', eventually_neg_of_eventually hfactor', hI.even] with t h1 h2 h3
  by_cases ht : t = 0
  · rw [ht, neg_zero]
  have h2' : I (-t) = t ^ (2 * k) * u (-t) := by
    rw [h2, Even.neg_pow ⟨k, by ring⟩]
  rw [h3, h1] at h2'
  exact (mul_left_cancel₀ (pow_ne_zero _ ht) h2').symm

end EvenPositiveResponse

namespace EvenPositiveResponse

/-- **Lemma 2.1, `(RP.3)`.**  `I = q²` near `0` with `q(t) = tᵏ h(t)`, where `h` is a positive even
analytic unit. -/
theorem exists_sqrt (hI : EvenPositiveResponse I k) :
    ∃ h : ℝ → ℝ, AnalyticAt ℝ h 0 ∧ 0 < h 0 ∧ (∀ᶠ t in 𝓝 0, 0 < h t) ∧
      (∀ᶠ t in 𝓝 0, h (-t) = h t) ∧ ∀ᶠ t in 𝓝 0, I t = (t ^ k * h t) ^ 2 := by
  obtain ⟨u, hu, hu0, hueven, hfactor⟩ := hI.exists_unit
  have hupos : ∀ᶠ t in 𝓝 0, 0 < u t :=
    (hu.continuousAt : Tendsto u (𝓝 0) (𝓝 (u 0))).eventually_const_lt hu0
  have hg : AnalyticAt ℝ (fun t => Real.exp (Real.log (u t) * (1 / 2))) 0 :=
    analyticAt_rexp.comp (((analyticAt_log hu0).comp hu).mul analyticAt_const)
  have heq : (fun t => Real.exp (Real.log (u t) * (1 / 2))) =ᶠ[𝓝 0] fun t => Real.sqrt (u t) := by
    filter_upwards [hupos] with t ht
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
  refine ⟨fun t => Real.sqrt (u t), hg.congr heq, Real.sqrt_pos.mpr hu0, ?_, ?_, ?_⟩
  · filter_upwards [hupos] with t ht
    exact Real.sqrt_pos.mpr ht
  · filter_upwards [hueven] with t ht
    rw [ht]
  · filter_upwards [hfactor, hupos] with t ht hpos
    rw [ht, mul_pow, Real.sq_sqrt hpos.le, ← pow_mul, mul_comm k 2]

end EvenPositiveResponse

/-- **Lemma 2.1, uniqueness.**  An analytic germ whose square agrees with `q²` is `q` or `-q`:
the germ ring is an integral domain (isolated zeros). -/
theorem eventuallyEq_or_eventuallyEq_neg_of_sq_eq {r q : ℝ → ℝ} (hr : AnalyticAt ℝ r 0)
    (hq : AnalyticAt ℝ q 0) (hsq : ∀ᶠ t in 𝓝 0, r t ^ 2 = q t ^ 2) :
    (r =ᶠ[𝓝 0] q) ∨ (r =ᶠ[𝓝 0] fun t => -q t) := by
  rcases (hr.sub hq).eventually_eq_zero_or_eventually_ne_zero with h1 | h1
  · left
    filter_upwards [h1] with t ht
    exact sub_eq_zero.mp ht
  rcases (hr.add hq).eventually_eq_zero_or_eventually_ne_zero with h2 | h2
  · right
    filter_upwards [h2] with t ht
    exact eq_neg_of_add_eq_zero_left ht
  exfalso
  obtain ⟨t, ht1, ht2, ht3⟩ := (h1.and (h2.and (nhdsWithin_le_nhds hsq))).exists
  have : (r t - q t) * (r t + q t) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · exact ht1 h
  · exact ht2 h

/-! ### Contact parity -/

/-- An analytic germ that does not vanish near `0` has exact contact data. -/
theorem exists_analyticContact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AnalyticAt ℝ f 0) (hne : ¬ ∀ᶠ t in 𝓝 0, f t = 0) :
    ∃ m a, AnalyticContact f m a := by
  have htop : analyticOrderAt f 0 ≠ ⊤ := by rwa [Ne, analyticOrderAt_eq_top]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨g, hg, hg0, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp hm.symm
  exact ⟨m, g 0, g, hg, rfl, hg0, by simpa using hfac⟩

/-- **An even contact has even order.** -/
theorem AnalyticContact.order_even_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {m : ℕ} {a : E} (hf : AnalyticContact f m a)
    (heven : ∀ᶠ t in 𝓝 0, f (-t) = f t) : Even m := by
  have hcomp : AnalyticContact (fun x => f (-x)) m ((-1 : ℝ) ^ m • a) := by
    simpa using hf.comp AnalyticContact.negId one_pos
  have hlead := hcomp.leading_eq_of_eventuallyEq hf heven
  have ha : a ≠ 0 := by
    rcases hf with ⟨_, _, _, ha, _⟩
    exact ha
  have hpow : (-1 : ℝ) ^ m = 1 := by
    have h0 : ((-1 : ℝ) ^ m - 1) • a = 0 := by rw [sub_smul, hlead, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right ha)
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hpow

/-- **An odd contact has odd order.** -/
theorem AnalyticContact.order_odd_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {m : ℕ} {a : E} (hf : AnalyticContact f m a)
    (hodd : ∀ᶠ t in 𝓝 0, f (-t) = -f t) : Odd m := by
  have hcomp : AnalyticContact (fun x => f (-x)) m ((-1 : ℝ) ^ m • a) := by
    simpa using hf.comp AnalyticContact.negId one_pos
  have hlead := hcomp.leading_eq_of_eventuallyEq hf.neg hodd
  have ha : a ≠ 0 := by
    rcases hf with ⟨_, _, _, ha, _⟩
    exact ha
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow, one_smul] at hlead
    have h2 : (2 : ℝ) • a = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hlead]
      exact add_neg_cancel a
    exact absurd ((smul_eq_zero.mp h2).resolve_left two_ne_zero) ha
  · exact ho

/-- Derivative of an eventually equivariant germ: `Γ(-t) = R Γ(t)` gives `Γ'(-t) = -R Γ'(t)`. -/
theorem eventually_deriv_neg_of_equivariant {Γ : ℝ → V} [CompleteSpace V] (hΓ : AnalyticAt ℝ Γ 0)
    (R : V →L[ℝ] V) (hequi : ∀ᶠ t in 𝓝 0, Γ (-t) = R (Γ t)) :
    ∀ᶠ t in 𝓝 0, deriv Γ (-t) = -R (deriv Γ t) := by
  have heq : (fun t => Γ (-t)) =ᶠ[𝓝 0] fun t => R (Γ t) := hequi
  filter_upwards [heq.deriv, eventually_differentiableAt_of_analyticAt hΓ] with t ht hdt
  have h1 : deriv (fun t => Γ (-t)) t = -deriv Γ (-t) := deriv_comp_neg Γ t
  have h2 : deriv (fun t => R (Γ t)) t = R (deriv Γ t) :=
    (R.hasFDerivAt.comp_hasDerivAt t hdt.hasDerivAt).deriv
  rw [h1, h2] at ht
  rw [← ht, neg_neg]

/-! ### Lower bounds -/

namespace OrientedRealization

variable [CompleteSpace V]

omit [CompleteSpace V] in
/-- The velocity of a realization does not vanish near `0`. -/
theorem velocity_not_eventually_zero (hI : EvenPositiveResponse I k)
    (ρ : OrientedRealization I V) : ¬ ∀ᶠ t in 𝓝 0, deriv ρ.curve t = 0 := by
  intro h
  apply hI.not_eventually_zero
  filter_upwards [h, ρ.speed] with t h1 h2
  rw [← h2, h1, norm_zero]
  norm_num

/-- **The velocity has contact order exactly `k`** (Gram doubling: `ν(‖Γ'‖²) = 2 ν(Γ')`). -/
theorem velocity_contact (hI : EvenPositiveResponse I k) (ρ : OrientedRealization I V) :
    ∃ a, AnalyticContact (deriv ρ.curve) k a := by
  obtain ⟨m, a, hc⟩ :=
    exists_analyticContact ρ.analyticAt.deriv (ρ.velocity_not_eventually_zero hI)
  have h1 := (positiveAnalyticContact_normSq hc).analyticOrderAt_eq
  have hspeed : (fun t => ‖deriv ρ.curve t‖ ^ (2 : ℕ)) =ᶠ[𝓝 0] I := ρ.speed
  rw [analyticOrderAt_congr hspeed, hI.order] at h1
  have hmk : m = k := by
    have := Nat.cast_injective (R := ℕ∞) h1
    omega
  exact ⟨a, hmk ▸ hc⟩

/-- `Γ'(-t) = -R Γ'(t)` near `0`. -/
theorem deriv_neg (ρ : OrientedRealization I V) :
    ∀ᶠ t in 𝓝 0, deriv ρ.curve (-t) = -ρ.refl (deriv ρ.curve t) :=
  eventually_deriv_neg_of_equivariant ρ.analyticAt
    ρ.refl.toLinearIsometry.toContinuousLinearMap ρ.equivariant

/-- **For odd half-order the involution is not `-1`**: `Γ'` would be even, so its contact order,
which is `k`, would be even. -/
theorem refl_ne_neg_of_odd (hI : EvenPositiveResponse I k) (hk : Odd k)
    (ρ : OrientedRealization I V) : ∃ v, ρ.refl v ≠ -v := by
  by_contra h
  push Not at h
  obtain ⟨a, hc⟩ := ρ.velocity_contact hI
  have heven : ∀ᶠ t in 𝓝 0, deriv ρ.curve (-t) = deriv ρ.curve t := by
    filter_upwards [ρ.deriv_neg] with t ht
    rw [ht, h, neg_neg]
  exact (Nat.not_even_iff_odd.mpr hk) (hc.order_even_of_even heven)

/-- **Theorem 3.1, odd half-order lower bound: `orrank(I) ≥ 2`.**  On a line every orthogonal
involution is `±1`. -/
theorem two_le_finrank [FiniteDimensional ℝ V] (hI : EvenPositiveResponse I k) (hk : Odd k)
    (ρ : OrientedRealization I V) : 2 ≤ Module.finrank ℝ V := by
  by_contra hlt
  have h1 : Module.finrank ℝ V = 1 := by
    have := ρ.finrank_pos
    omega
  obtain ⟨e, he, hspan⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨c, hc⟩ := hspan (ρ.refl e)
  have hR : ∀ v, ρ.refl v = c • v := by
    intro v
    obtain ⟨d, rfl⟩ := hspan v
    rw [map_smul, ← hc, smul_comm]
  have hc2 : c * c = 1 := by
    have h := ρ.refl_refl e
    rw [hR, hR, smul_smul] at h
    have h0 : (c * c - 1) • e = 0 := by rw [sub_smul, h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right he)
  rcases mul_self_eq_one_iff.mp hc2 with h | h
  · obtain ⟨v, hv⟩ := ρ.refl_ne_id
    exact hv (by rw [hR, h, one_smul])
  · obtain ⟨v, hv⟩ := ρ.refl_ne_neg_of_odd hI hk
    exact hv (by rw [hR, h, neg_one_smul])

end OrientedRealization

/-! ### Constructions -/

/-- An odd germ positive on `(0, δ)` separates the two sides of `0`. -/
theorem eventually_ne_neg_of_pos_of_odd {g : ℝ → ℝ} (hpos : ∀ᶠ t in 𝓝[>] 0, 0 < g t)
    (hodd : ∀ᶠ t in 𝓝 0, g (-t) = -g t) : ∀ᶠ t in 𝓝[≠] 0, g t ≠ g (-t) := by
  obtain ⟨ε, hε, hεpos⟩ := Metric.mem_nhdsWithin_iff.mp hpos
  obtain ⟨δ, hδ, hδodd⟩ := Metric.eventually_nhds_iff.mp hodd
  refine Metric.mem_nhdsWithin_iff.mpr ⟨min ε δ, lt_min hε hδ, fun t ⟨ht, ht0⟩ => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  have hε' : |t| < ε := ht.trans_le (min_le_left _ _)
  have hδ' : |t| < δ := ht.trans_le (min_le_right _ _)
  have hodd_t : g (-t) = -g t := hδodd (by rw [Real.dist_eq, sub_zero]; exact hδ')
  show g t ≠ g (-t)
  rcases lt_or_gt_of_ne (show t ≠ 0 from ht0) with hneg | hpos'
  · have hgt : 0 < g (-t) := hεpos
      ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg]; exact hε', neg_pos.mpr hneg⟩
    intro h
    linarith
  · have hgt : 0 < g t := hεpos ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hε', hpos'⟩
    intro h
    linarith

/-- Pythagoras for an orthonormal pair. -/
theorem norm_smul_add_smul_sq {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (a b : ℝ) : ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, huv, norm_smul, norm_smul,
    hu, hv, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, sq_abs, sq_abs]
  ring

theorem inner_smul_add_smul_right {u v : V} (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (a b : ℝ) :
    ⟪v, a • u + b • v⟫_ℝ = b := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm, huv,
    real_inner_self_eq_norm_sq, hv]
  ring

namespace EvenPositiveResponse

/-- The analytic square root `q(t) = tᵏ h(t)` and its basic properties. -/
theorem exists_sqrt' (hI : EvenPositiveResponse I k) :
    ∃ q : ℝ → ℝ, AnalyticAt ℝ q 0 ∧ (∀ᶠ t in 𝓝 0, I t = q t ^ 2) ∧
      (∀ᶠ t in 𝓝 0, q (-t) = (-1) ^ k * q t) ∧ (∀ᶠ t in 𝓝[>] 0, 0 < q t) := by
  obtain ⟨h, hh, -, hhpos, hheven, hsq⟩ := hI.exists_sqrt
  refine ⟨fun t => t ^ k * h t, (analyticAt_id.pow k).mul hh, hsq, ?_, ?_⟩
  · filter_upwards [hheven] with t ht
    rw [ht, neg_pow]
    ring
  · filter_upwards [nhdsWithin_le_nhds hhpos, self_mem_nhdsWithin] with t ht ht0
    exact mul_pos (pow_pos ht0 k) ht

/-- The line realization `Γ = ∫₀ᵗ q`, `R = -1`, of an even square root `q` positive on `(0, δ)`. -/
theorem exists_lineRealization_of_sqrt {q : ℝ → ℝ} (hq : AnalyticAt ℝ q 0)
    (hsq : ∀ᶠ t in 𝓝 0, I t = q t ^ 2) (hqeven : ∀ᶠ t in 𝓝 0, q (-t) = q t)
    (hqpos : ∀ᶠ t in 𝓝[>] 0, 0 < q t) :
    ∃ ρ : OrientedRealization I ℝ, ρ.curve = primitiveAtZero q := by
  have hodd := primitiveAtZero_neg_of_even hqeven
  exact ⟨{ refl := LinearIsometryEquiv.neg ℝ (E := ℝ)
           refl_refl := fun v => by simp
           curve := primitiveAtZero q
           analyticAt := analyticAt_primitiveAtZero hq
           curve_zero := primitiveAtZero_zero q
           equivariant := by
             filter_upwards [hodd] with t ht
             simpa using ht
           speed := by
             filter_upwards [eventually_hasDerivAt_primitiveAtZero hq, hsq] with t ht hst
             rw [ht.deriv, Real.norm_eq_abs, sq_abs, hst]
           separated :=
             eventually_ne_neg_of_pos_of_odd (eventually_primitiveAtZero_pos hq hqpos) hodd }, rfl⟩

/-- **Theorem 3.1, even half-order: a realization on the line**, `Γ = ∫₀ᵗ q` with `R = -1`
`(RP.5)`. -/
theorem exists_lineRealization (hI : EvenPositiveResponse I k) (hk : Even k) :
    Nonempty (OrientedRealization I ℝ) := by
  obtain ⟨q, hq, hsq, hqpar, hqpos⟩ := hI.exists_sqrt'
  have hqeven : ∀ᶠ t in 𝓝 0, q (-t) = q t := by
    filter_upwards [hqpar] with t ht
    rw [ht, hk.neg_one_pow, one_mul]
  obtain ⟨ρ, -⟩ := exists_lineRealization_of_sqrt hq hsq hqeven hqpos
  exact ⟨ρ⟩

/-- **Theorem 3.1, odd half-order: a realization in the plane `(RP.6)`.**  For any orthogonal
involution with a fixed unit vector `uf` and an orthogonal reversed unit vector `ur`,
`Γ(t) = (∫₀ᵗ q cos) uf + (∫₀ᵗ q sin) ur` realizes `I`. -/
theorem exists_planeRealization (hI : EvenPositiveResponse I k) (hk : Odd k) [CompleteSpace V]
    (R : V ≃ₗᵢ[ℝ] V) (hR : ∀ v, R (R v) = v) {uf ur : V} (huf : ‖uf‖ = 1) (hur : ‖ur‖ = 1)
    (horth : ⟪uf, ur⟫_ℝ = 0) (hRf : R uf = uf) (hRr : R ur = -ur) :
    ∃ ρ : OrientedRealization I V, ρ.refl = R := by
  obtain ⟨q, hq, hsq, hqpar, hqpos⟩ := hI.exists_sqrt'
  have hqodd : ∀ᶠ t in 𝓝 0, q (-t) = -q t := by
    filter_upwards [hqpar] with t ht
    rw [ht, hk.neg_one_pow, neg_one_mul]
  set c : ℝ → ℝ := fun t => q t * Real.cos t
  set s : ℝ → ℝ := fun t => q t * Real.sin t
  have hc : AnalyticAt ℝ c 0 := hq.mul Real.analyticAt_cos
  have hs : AnalyticAt ℝ s 0 := hq.mul Real.analyticAt_sin
  have hcodd : ∀ᶠ t in 𝓝 0, c (-t) = -c t := by
    filter_upwards [hqodd] with t ht
    simp only [c, ht, Real.cos_neg, neg_mul]
  have hseven : ∀ᶠ t in 𝓝 0, s (-t) = s t := by
    filter_upwards [hqodd] with t ht
    simp only [s, ht, Real.sin_neg, neg_mul_neg]
  have h1even := primitiveAtZero_neg_of_odd hcodd
  have h2odd := primitiveAtZero_neg_of_even hseven
  have hspos : ∀ᶠ t in 𝓝[>] 0, 0 < s t := by
    filter_upwards [hqpos, self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds Real.pi_pos)]
      with t ht ht0 htpi
    exact mul_pos ht (Real.sin_pos_of_pos_of_lt_pi ht0 htpi)
  have h2sep := eventually_ne_neg_of_pos_of_odd (eventually_primitiveAtZero_pos hs hspos) h2odd
  set Γ : ℝ → V := fun t => primitiveAtZero c t • uf + primitiveAtZero s t • ur
  refine ⟨{ refl := R
            refl_refl := hR
            curve := Γ
            analyticAt := ((analyticAt_primitiveAtZero hc).smul analyticAt_const).add
              ((analyticAt_primitiveAtZero hs).smul analyticAt_const)
            curve_zero := by simp [Γ, primitiveAtZero_zero]
            equivariant := ?_
            speed := ?_
            separated := ?_ }, rfl⟩
  · filter_upwards [h1even, h2odd] with t h1 h2
    simp only [Γ, h1, h2, map_add, map_smul, hRf, hRr, neg_smul, smul_neg]
  · filter_upwards [eventually_hasDerivAt_primitiveAtZero hc,
      eventually_hasDerivAt_primitiveAtZero hs, hsq] with t hd1 hd2 hst
    have hd : HasDerivAt Γ (c t • uf + s t • ur) t := (hd1.smul_const uf).add (hd2.smul_const ur)
    rw [hd.deriv, norm_smul_add_smul_sq huf hur horth, hst]
    simp only [c, s, mul_pow]
    rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  · filter_upwards [h2sep] with t ht heq
    apply ht
    have h := congrArg (fun v => ⟪ur, v⟫_ℝ) heq
    simpa only [Γ, inner_smul_add_smul_right hur horth] using h

end EvenPositiveResponse

/-! ### The sheet swap -/

/-- The sheet swap of the two-sheet packet: the permutation representation of `ℤ/2` on `ℝ²`. -/
def sheetSwap : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

theorem sheetSwap_single_zero :
    sheetSwap (EuclideanSpace.single 0 1) = EuclideanSpace.single 1 1 := by
  rw [sheetSwap, EuclideanSpace.piLpCongrLeft_single, Equiv.swap_apply_left]

theorem sheetSwap_single_one :
    sheetSwap (EuclideanSpace.single 1 1) = EuclideanSpace.single 0 1 := by
  rw [sheetSwap, EuclideanSpace.piLpCongrLeft_single, Equiv.swap_apply_right]

/-- The symmetric sheet vector `e₊ = (1, 1)/√2`. -/
def sheetPlus : EuclideanSpace ℝ (Fin 2) :=
  (Real.sqrt 2)⁻¹ • (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1)

/-- The antisymmetric sheet vector `e₋ = (1, -1)/√2`. -/
def sheetMinus : EuclideanSpace ℝ (Fin 2) :=
  (Real.sqrt 2)⁻¹ • (EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1)

theorem sheetSwap_sheetPlus : sheetSwap sheetPlus = sheetPlus := by
  rw [sheetPlus, map_smul, map_add, sheetSwap_single_zero, sheetSwap_single_one, add_comm]

theorem sheetSwap_sheetMinus : sheetSwap sheetMinus = -sheetMinus := by
  rw [sheetMinus, map_smul, map_sub, sheetSwap_single_zero, sheetSwap_single_one, ← smul_neg,
    neg_sub]

theorem sheetSwap_sheetSwap (v : EuclideanSpace ℝ (Fin 2)) : sheetSwap (sheetSwap v) = v := by
  ext i
  fin_cases i <;> simp [sheetSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem sheet_orthonormal :
    ‖sheetPlus‖ = 1 ∧ ‖sheetMinus‖ = 1 ∧ ⟪sheetPlus, sheetMinus⟫_ℝ = 0 := by
  have hon := EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 2)
  have h0 : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := hon.1 0
  have h1 : ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := hon.1 1
  have h01 : ⟪(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)),
      EuclideanSpace.single 1 1⟫_ℝ = 0 := hon.2 (by decide)
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnorm : ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ ^ 2 = 2 → ‖(Real.sqrt 2)⁻¹ • v‖ = 1 := by
    intro v hv
    have hv' : ‖v‖ = Real.sqrt 2 := by
      rw [← Real.sqrt_sq (norm_nonneg v), hv]
    rw [norm_smul, hv', Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity),
      inv_mul_cancel₀ hs2]
  refine ⟨hnorm _ ?_, hnorm _ ?_, ?_⟩
  · rw [norm_add_sq_real, h0, h1, h01]
    norm_num
  · rw [norm_sub_sq_real, h0, h1, h01]
    norm_num
  · rw [sheetPlus, sheetMinus, real_inner_smul_left, real_inner_smul_right, inner_add_left,
      inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      h0, h1, h01, real_inner_comm, h01]
    ring

/-- **The two-sheet packet realizes every odd half-order response with its sheet swap.** -/
theorem EvenPositiveResponse.exists_sheetRealization (hI : EvenPositiveResponse I k)
    (hk : Odd k) : ∃ ρ : OrientedRealization I (EuclideanSpace ℝ (Fin 2)), ρ.refl = sheetSwap :=
  hI.exists_planeRealization hk sheetSwap sheetSwap_sheetSwap sheet_orthonormal.1
    sheet_orthonormal.2.1 sheet_orthonormal.2.2 sheetSwap_sheetPlus sheetSwap_sheetMinus

/-! ### Theorem 3.1 -/

/-- **Theorem 3.1, `(RP.4)`: the reflection-contact rank law.**
`orrank(I) = 1` for even `k` and `orrank(I) = 2` for odd `k`. -/
theorem EvenPositiveResponse.orientedRank_eq (hI : EvenPositiveResponse I k) :
    orientedRank I = if Even k then 1 else 2 := by
  have hlow : ∀ n, Nonempty (OrientedRealization I (EuclideanSpace ℝ (Fin n))) →
      (if Even k then 1 else 2) ≤ n := by
    rintro n ⟨ρ⟩
    split_ifs with hk
    · have := ρ.finrank_pos
      rwa [finrank_euclideanSpace_fin] at this
    · have := ρ.two_le_finrank hI (Nat.not_even_iff_odd.mp hk)
      rwa [finrank_euclideanSpace_fin] at this
  split_ifs with hk
  · obtain ⟨ρ⟩ := hI.exists_lineRealization hk
    have hle := ρ.orientedRank_le
    rw [Module.finrank_self] at hle
    have hmem := Nat.sInf_mem (s := {n : ℕ | Nonempty (OrientedRealization I
      (EuclideanSpace ℝ (Fin n)))}) ⟨_, ⟨ρ.toEuclidean⟩⟩
    have := hlow _ hmem
    rw [if_pos hk] at this
    exact le_antisymm hle this
  · obtain ⟨ρ, -⟩ := hI.exists_sheetRealization (Nat.not_even_iff_odd.mp hk)
    have hle := ρ.orientedRank_le
    rw [finrank_euclideanSpace_fin] at hle
    have hmem := Nat.sInf_mem (s := {n : ℕ | Nonempty (OrientedRealization I
      (EuclideanSpace ℝ (Fin n)))}) ⟨_, ⟨ρ⟩⟩
    have := hlow _ hmem
    rw [if_neg hk] at this
    exact le_antisymm hle this

/-! ### Corollary 3.2 -/

/-- In a plane, an orthonormal pair is an orthonormal basis. -/
theorem eq_inner_smul_add_inner_smul [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V = 2)
    {ef er : V} (hef : ‖ef‖ = 1) (her : ‖er‖ = 1) (horth : ⟪ef, er⟫_ℝ = 0) (v : V) :
    v = ⟪ef, v⟫_ℝ • ef + ⟪er, v⟫_ℝ • er := by
  have hon : Orthonormal ℝ ![ef, er] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hef, her, horth, real_inner_comm]
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hrange : Set.range ![ef, er] = {ef, er} := by
    ext x
    simp [eq_comm, or_comm]
  rw [hrange] at hspan
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hspan ▸ Submodule.mem_top : v ∈ _)
  have ha : ⟪ef, v⟫_ℝ = a := by
    rw [← hab, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hef, horth]
    ring
  have hb : ⟪er, v⟫_ℝ = b := by
    rw [← hab, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, her, real_inner_comm, horth]
    ring
  rw [ha, hb, hab]

namespace OrientedRealization

variable [CompleteSpace V]

omit [CompleteSpace V] in
/-- An orthogonal involution is self-adjoint. -/
theorem inner_refl (ρ : OrientedRealization I V) (e w : V) :
    ⟪e, ρ.refl w⟫_ℝ = ⟪ρ.refl e, w⟫_ℝ := by
  rw [← ρ.refl.inner_map_map (ρ.refl e) w, ρ.refl_refl]

/-- **Corollary 3.2: forced representation type.**  For odd half-order, a realization in a plane
has an orthonormal eigenbasis `ef, er` with `R ef = ef`, `R er = -er`; in it `R = diag(1, -1)`. -/
theorem exists_eigenbasis [FiniteDimensional ℝ V] (hI : EvenPositiveResponse I k) (hk : Odd k)
    (ρ : OrientedRealization I V) (hV : Module.finrank ℝ V = 2) :
    ∃ ef er : V, ‖ef‖ = 1 ∧ ‖er‖ = 1 ∧ ⟪ef, er⟫_ℝ = 0 ∧ ρ.refl ef = ef ∧ ρ.refl er = -er ∧
      ∀ v, ρ.refl v = ⟪ef, v⟫_ℝ • ef - ⟪er, v⟫_ℝ • er := by
  obtain ⟨w, hw⟩ := ρ.refl_ne_neg_of_odd hI hk
  obtain ⟨v, hv⟩ := ρ.refl_ne_id
  set x := w + ρ.refl w
  set y := v - ρ.refl v
  have hx : x ≠ 0 := fun h => hw (eq_neg_of_add_eq_zero_right h)
  have hy : y ≠ 0 := fun h => hv (sub_eq_zero.mp h).symm
  have hRx : ρ.refl x = x := by simp only [x, map_add, ρ.refl_refl, add_comm]
  have hRy : ρ.refl y = -y := by simp only [y, map_sub, ρ.refl_refl, neg_sub]
  set ef := ‖x‖⁻¹ • x
  set er := ‖y‖⁻¹ • y
  have hef : ‖ef‖ = 1 := norm_smul_inv_norm hx
  have her : ‖er‖ = 1 := norm_smul_inv_norm hy
  have hRf : ρ.refl ef = ef := by rw [map_smul, hRx]
  have hRr : ρ.refl er = -er := by rw [map_smul, hRy, smul_neg]
  clear_value ef er
  have horth : ⟪ef, er⟫_ℝ = 0 := by
    have h := ρ.refl.inner_map_map ef er
    rw [hRf, hRr, inner_neg_right] at h
    linarith
  refine ⟨ef, er, hef, her, horth, hRf, hRr, fun u => ?_⟩
  conv_lhs => rw [eq_inner_smul_add_inner_smul hV hef her horth u]
  rw [map_add, map_smul, map_smul, hRf, hRr, smul_neg, sub_eq_add_neg]

/-- **Corollary 3.2, `(RP.7a)`: orientation latency.**  For odd half-order and an orthonormal
eigenbasis of a plane realization, the velocity in the fixed channel has contact order exactly `k`,
and the velocity in the reversed channel has even order strictly larger than `k`. -/
theorem channel_orders [FiniteDimensional ℝ V] (hI : EvenPositiveResponse I k) (hk : Odd k)
    (ρ : OrientedRealization I V) (hV : Module.finrank ℝ V = 2) {ef er : V} (hef : ‖ef‖ = 1)
    (her : ‖er‖ = 1) (horth : ⟪ef, er⟫_ℝ = 0) (hRf : ρ.refl ef = ef) (hRr : ρ.refl er = -er) :
    analyticOrderAt (fun t => ⟪ef, deriv ρ.curve t⟫_ℝ) 0 = k ∧
      ∃ m : ℕ, analyticOrderAt (fun t => ⟪er, deriv ρ.curve t⟫_ℝ) 0 = m ∧ k < m ∧ Even m := by
  set vf : ℝ → ℝ := fun t => ⟪ef, deriv ρ.curve t⟫_ℝ
  set vr : ℝ → ℝ := fun t => ⟪er, deriv ρ.curve t⟫_ℝ
  have hvf : AnalyticAt ℝ vf 0 := analyticAt_inner analyticAt_const ρ.analyticAt.deriv
  have hvr : AnalyticAt ℝ vr 0 := analyticAt_inner analyticAt_const ρ.analyticAt.deriv
  have hvf_odd : ∀ᶠ t in 𝓝 0, vf (-t) = -vf t := by
    filter_upwards [ρ.deriv_neg] with t ht
    simp only [vf, ht, inner_neg_right, ρ.inner_refl, hRf]
  have hvr_even : ∀ᶠ t in 𝓝 0, vr (-t) = vr t := by
    filter_upwards [ρ.deriv_neg] with t ht
    simp only [vr, ht, inner_neg_right, ρ.inner_refl, hRr, inner_neg_left, neg_neg]
  have hsum : (fun t => ‖vf t‖ ^ (2 : ℕ) + ‖vr t‖ ^ (2 : ℕ)) =ᶠ[𝓝 0] I := by
    filter_upwards [ρ.speed] with t ht
    rw [← ht, eq_inner_smul_add_inner_smul hV hef her horth (deriv ρ.curve t),
      norm_smul_add_smul_sq hef her horth, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  -- the reversed channel does not vanish: otherwise the curve would fold
  have hvr_ne : ¬ ∀ᶠ t in 𝓝 0, vr t = 0 := by
    intro h0
    have hderiv : ∀ᶠ t in 𝓝 0, HasDerivAt (fun t => ⟪er, ρ.curve t⟫_ℝ) 0 t := by
      filter_upwards [h0, eventually_differentiableAt_of_analyticAt ρ.analyticAt] with t ht hd
      have h := ((innerSL ℝ er).hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt)
      simp only [innerSL_apply_apply] at h
      rwa [show ⟪er, deriv ρ.curve t⟫_ℝ = vr t from rfl, ht] at h
    have hzero : ∀ᶠ t in 𝓝 0, ⟪er, ρ.curve t⟫_ℝ = 0 := by
      filter_upwards [eventually_forall_uIcc hderiv] with t ht
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := fun _ => (0 : ℝ)) ht
        intervalIntegrable_const
      simp only [intervalIntegral.integral_zero, ρ.curve_zero, inner_zero_right, sub_zero] at h
      exact h.symm
    obtain ⟨t, hsep, hz, hzn, hequi⟩ := (ρ.separated.and (nhdsWithin_le_nhds
      (hzero.and ((eventually_neg_of_eventually hzero).and ρ.equivariant)))).exists
    apply hsep
    rw [eq_inner_smul_add_inner_smul hV hef her horth (ρ.curve t),
      eq_inner_smul_add_inner_smul hV hef her horth (ρ.curve (-t)), hz, hzn, hequi,
      ρ.inner_refl, hRf]
  obtain ⟨mr, ar, hcr⟩ := exists_analyticContact hvr hvr_ne
  have hmr : Even mr := hcr.order_even_of_even hvr_even
  have hPr := positiveAnalyticContact_normSq hcr
  -- the fixed channel does not vanish: otherwise `ν(I) = 2 ν(vr) ≡ 0 mod 4`
  have hvf_ne : ¬ ∀ᶠ t in 𝓝 0, vf t = 0 := by
    intro h0
    have heq : (fun t => ‖vr t‖ ^ (2 : ℕ)) =ᶠ[𝓝 0] I := by
      filter_upwards [hsum, h0] with t ht h0t
      rw [← ht, h0t, norm_zero]
      ring
    have h := hPr.analyticOrderAt_eq
    rw [analyticOrderAt_congr heq, hI.order] at h
    have h' := Nat.cast_injective (R := ℕ∞) h
    have hkm : k = mr := by omega
    exact (Nat.not_even_iff_odd.mpr hk) (hkm ▸ hmr)
  obtain ⟨mf, af, hcf⟩ := exists_analyticContact hvf hvf_ne
  have hmf : Odd mf := hcf.order_odd_of_odd hvf_odd
  have hPf := positiveAnalyticContact_normSq hcf
  have hmin := PositiveAnalyticContact.analyticOrderAt_add_eq_min hPf hPr
  rw [analyticOrderAt_congr hsum, hI.order] at hmin
  have hmin' : 2 * k = min (2 * mf) (2 * mr) := by exact_mod_cast hmin
  have hkf : k = mf := by
    rcases min_choice (2 * mf) (2 * mr) with h | h
    · omega
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hk) (show k = mr by omega ▸ hmr)
  refine ⟨by rw [hcf.analyticOrderAt_eq, hkf], mr, hcr.analyticOrderAt_eq, ?_, hmr⟩
  have hle : k ≤ mr := by omega
  rcases hle.lt_or_eq with h | h
  · exact h
  · exact absurd (h ▸ hmr) (Nat.not_even_iff_odd.mpr hk)

end OrientedRealization

/-! ### §6: the Wold response and the sheet packet -/

/-- The Wold response `I_W(u) = cosh u - sinh u / u` `(RP.14)`, continuously extended by `0`. -/
abbrev woldResponse : ℝ → ℝ := RHTower.sourceHorizontalWoldPrimeClockResponse

theorem woldResponse_eq_cosh_sub_dslope :
    woldResponse = fun u => Real.cosh u - dslope Real.sinh 0 u := by
  funext u
  show RHTower.sourceHorizontalWoldPrimeClockResponse u = _
  rw [RHTower.sourceHorizontalWoldPrimeClockResponse_eq_cosh_sub_sinhc]
  congr 1
  by_cases hu : u = 0
  · subst hu
    rw [RHTower.woldRemovableSinhc_zero, dslope_same, Real.deriv_sinh, Real.cosh_zero]
  · rw [RHTower.woldRemovableSinhc_eq hu, dslope_of_ne _ hu, slope_def_field, Real.sinh_zero,
      sub_zero, sub_zero]

theorem analyticAt_woldResponse : AnalyticAt ℝ woldResponse 0 := by
  rw [woldResponse_eq_cosh_sub_dslope]
  obtain ⟨p, hp⟩ := (Real.analyticAt_sinh (x := 0))
  exact Real.analyticAt_cosh.sub ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- **`ν(I_W) = 2`**: the Wold response is an even positive response of half-order `k = 1`. -/
theorem woldResponse_evenPositive : EvenPositiveResponse woldResponse 1 := by
  have hW := analyticAt_woldResponse
  have hzero : woldResponse 0 = 0 := RHTower.sourceHorizontalWoldPrimeClockResponse_zero
  have hnonneg : ∀ᶠ t in 𝓝 0, 0 ≤ woldResponse t := Eventually.of_forall fun t =>
    le_trans (by positivity) (RHTower.sourceHorizontalWoldPrimeClockResponse_quadratic_lower t)
  have hfinite : analyticOrderAt woldResponse 0 ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro h
    have h' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), woldResponse t = 0 := nhdsWithin_le_nhds h
    obtain ⟨t, ht, ht0⟩ := (h'.and self_mem_nhdsWithin).exists
    exact ht0 ((RHTower.sourceHorizontalWoldPrimeClockResponse_eq_zero_iff t).mp ht)
  obtain ⟨a, hpos, hmpos⟩ :=
    PositiveAnalyticContact.exists_of_analytic_zero_eventually_nonnegative hW hzero hfinite hnonneg
  set m := (analyticOrderAt woldResponse 0).toNat
  have hmeven : Even m := hpos.order_even
  have hm2 : m = 2 := by
    by_contra hne
    have hm4 : 2 < m := by
      rcases hmeven with ⟨j, hj⟩
      omega
    obtain ⟨⟨u, hu, -, -, hfac⟩, -, -⟩ := hpos
    have htend : Tendsto (fun t : ℝ => t ^ (m - 2) * u t) (𝓝 0) (𝓝 0) := by
      have h : ContinuousAt (fun t : ℝ => t ^ (m - 2) * u t) 0 :=
        (continuousAt_id.pow (m - 2)).mul hu.continuousAt
      simpa [zero_pow (by omega : m - 2 ≠ 0)] using h.tendsto
    have hsmall : ∀ᶠ t in 𝓝 0, t ^ (m - 2) * u t < 1 / 3 :=
      htend.eventually (gt_mem_nhds (by norm_num))
    have hboth : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ^ (m - 2) * u t < 1 / 3 ∧
        woldResponse t = t ^ m • u t := nhdsWithin_le_nhds (hsmall.and hfac)
    obtain ⟨t, ⟨hs, hf⟩, ht0⟩ := (hboth.and self_mem_nhdsWithin).exists
    have hlow : t ^ 2 / 3 ≤ woldResponse t :=
      RHTower.sourceHorizontalWoldPrimeClockResponse_quadratic_lower t
    rw [hf, smul_eq_mul] at hlow
    have ht2 : 0 < t ^ 2 := by
      have : t ≠ 0 := ht0
      positivity
    have hsplit : t ^ m = t ^ 2 * t ^ (m - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, mul_assoc] at hlow
    have : 1 / 3 ≤ t ^ (m - 2) * u t := by
      by_contra hlt
      push Not at hlt
      nlinarith
    linarith
  refine ⟨hW, Eventually.of_forall fun t =>
    RHTower.sourceHorizontalWoldPrimeClockResponse_even t, hnonneg, hzero, ?_⟩
  rw [← ENat.coe_toNat hfinite]
  change ((m : ℕ) : ℕ∞) = _
  rw [hm2]

/-- **`(RP.15)`: `orrank(I_W) = 2`.** -/
theorem orientedRank_woldResponse : orientedRank woldResponse = 2 := by
  rw [woldResponse_evenPositive.orientedRank_eq]
  simp

/-- **The sheet swap realizes the Wold response**: the two-sheet packet is a minimal oriented
realization, with exactly the forced involution type (one trivial, one sign channel). -/
theorem exists_woldSheetRealization :
    ∃ ρ : OrientedRealization woldResponse (EuclideanSpace ℝ (Fin 2)), ρ.refl = sheetSwap :=
  woldResponse_evenPositive.exists_sheetRealization odd_one

/-! ### §7: reflection-compatible ramification -/

/-- **§7.**  An odd analytic ramification `φ` of order `r` sends a response of half-order `k` to a
response of half-order `r k`. -/
theorem EvenPositiveResponse.comp_odd (hI : EvenPositiveResponse I k) {φ : ℝ → ℝ} {r : ℕ} {b : ℝ}
    (hφ : AnalyticContact φ r b) (hr : 0 < r) (hodd : ∀ᶠ t in 𝓝 0, φ (-t) = -φ t) :
    EvenPositiveResponse (fun t => I (φ t)) (r * k) := by
  have hφ0 : φ 0 = 0 := by
    rcases hφ with ⟨u, -, -, -, hfac⟩
    have h := hfac.self_of_nhds
    simpa [Nat.ne_of_gt hr] using h
  have hφa := hφ.analyticAt
  have htend : Tendsto φ (𝓝 0) (𝓝 0) := by simpa [hφ0] using hφa.continuousAt.tendsto
  obtain ⟨g, hg, hg0, hfac⟩ := hI.analyticAt.analyticOrderAt_eq_natCast.mp hI.order
  have hcI : AnalyticContact I (2 * k) (g 0) := ⟨g, hg, rfl, hg0, by simpa using hfac⟩
  refine ⟨?_, ?_, htend.eventually hI.nonneg, by simp [hφ0, hI.zero], ?_⟩
  · have hIa : AnalyticAt ℝ I (φ 0) := by rw [hφ0]; exact hI.analyticAt
    exact hIa.comp hφa
  · filter_upwards [hodd, htend.eventually hI.even] with t h1 h2
    rw [h1, h2]
  · rw [analyticOrderAt_comp_eq_mul hcI hφ hr]
    push_cast
    ring

/-- **§7.  The oriented rank is invariant under reflection-compatible ramification.** -/
theorem EvenPositiveResponse.orientedRank_comp_odd (hI : EvenPositiveResponse I k) {φ : ℝ → ℝ}
    {r : ℕ} {b : ℝ} (hφ : AnalyticContact φ r b) (hr : 0 < r)
    (hodd : ∀ᶠ t in 𝓝 0, φ (-t) = -φ t) :
    orientedRank (fun t => I (φ t)) = orientedRank I := by
  rw [(hI.comp_odd hφ hr hodd).orientedRank_eq, hI.orientedRank_eq]
  simp only [halfOrder_parity_iff_of_antireflection hφ hr hodd]

/-! ### Germ invariance -/

namespace OrientedRealization

/-- A realization may replace its curve by any germ-equal curve. -/
def congrCurve [CompleteSpace V] (ρ : OrientedRealization I V) (c : ℝ → V)
    (hc : c =ᶠ[𝓝 0] ρ.curve) : OrientedRealization I V where
  refl := ρ.refl
  refl_refl := ρ.refl_refl
  curve := c
  analyticAt := ρ.analyticAt.congr hc.symm
  curve_zero := by rw [hc.self_of_nhds, ρ.curve_zero]
  equivariant := by
    filter_upwards [hc, eventually_neg_of_eventually hc, ρ.equivariant] with t h1 h2 h3
    rw [h2, h3, h1]
  speed := by
    filter_upwards [hc.deriv, ρ.speed] with t h1 h2
    rw [h1, h2]
  separated := by
    filter_upwards [nhdsWithin_le_nhds hc, nhdsWithin_le_nhds (eventually_neg_of_eventually hc),
      ρ.separated] with t h1 h2 h3
    rw [h1, h2]
    exact h3

/-- A realization of `I` realizes every response germ-equal to `I`. -/
def ofEventuallyEq (ρ : OrientedRealization I V) {J : ℝ → ℝ} (hIJ : I =ᶠ[𝓝 0] J) :
    OrientedRealization J V :=
  { ρ with
    speed := by
      filter_upwards [ρ.speed, hIJ] with t h1 h2
      rw [h1, h2] }

end OrientedRealization

/-- `orrank` depends only on the germ of the response. -/
theorem orientedRank_congr {J : ℝ → ℝ} (hIJ : I =ᶠ[𝓝 0] J) :
    orientedRank I = orientedRank J := by
  unfold orientedRank
  congr 1
  ext n
  exact ⟨fun ⟨ρ⟩ => ⟨ρ.ofEventuallyEq hIJ⟩, fun ⟨ρ⟩ => ⟨ρ.ofEventuallyEq hIJ.symm⟩⟩

end GaloisForLFunctions.HTGeometry
