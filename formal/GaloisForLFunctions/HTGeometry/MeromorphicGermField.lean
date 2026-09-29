import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing
import GaloisForLFunctions.HTGeometry.RationalPolarCalculus

/-!
# The field of meromorphic germs at the origin

Germs along the punctured neighbourhood filter `𝓝[≠] 0` of functions meromorphic at `0` form a
field `MeroGerm`: a nonzero germ has finite order, so it is eventually nonzero off the origin and
its
pointwise inverse inverts it.

* **Derivation.**  Two functions agreeing on a punctured neighbourhood have derivatives agreeing on
  a punctured neighbourhood, so `d/dz` descends to a derivation of `MeroGerm`.
* **Rational functions.**  `ℂ(z)` embeds, a rational function going to the germ of its values; the
  derivative of the value function of `Q` is the value function of `Q'` wherever the reduced
  denominator does not vanish.
* **Pullback.**  An analytic map fixing the origin with nonzero derivative there maps the punctured
  neighbourhood filter to itself, and precomposition with it is a ring endomorphism of `MeroGerm`
  obeying the chain rule.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The field -/

/-- Germs off the origin represented by a function meromorphic at the origin. -/
def meroGermSubring : Subring (Germ (𝓝[≠] (0 : ℂ)) ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, MeromorphicAt f 0 ∧ (f : Germ (𝓝[≠] (0 : ℂ)) ℂ) = g}
  zero_mem' := ⟨fun _ => 0, MeromorphicAt.const 0 0, rfl⟩
  one_mem' := ⟨fun _ => 1, MeromorphicAt.const 1 0, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

/-- **A nonzero meromorphic germ is invertible.** -/
theorem exists_inv_meroGerm {g : Germ (𝓝[≠] (0 : ℂ)) ℂ} (hg : g ∈ meroGermSubring) (hne : g ≠ 0) :
    ∃ h ∈ meroGermSubring, g * h = 1 := by
  obtain ⟨f, hf, rfl⟩ := hg
  have hnetop : meromorphicOrderAt f 0 ≠ ⊤ := by
    intro htop
    exact hne (Germ.coe_eq.mpr (meromorphicOrderAt_eq_top_iff.mp htop))
  refine ⟨(f⁻¹ : ℂ → ℂ), ⟨f⁻¹, hf.inv, rfl⟩, ?_⟩
  have hev := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp hnetop
  exact Germ.coe_eq.mpr (hev.mono fun z hz => by simp [hz])

theorem one_ne_zero_meroGerm :
    ((fun _ => (1 : ℂ) : ℂ → ℂ) : Germ (𝓝[≠] (0 : ℂ)) ℂ)
      ≠ ((fun _ => (0 : ℂ) : ℂ → ℂ) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
  intro h
  obtain ⟨z, hz⟩ := (Germ.coe_eq.mp h).exists
  exact one_ne_zero hz

/-- **The field of meromorphic germs at the origin.** -/
def MeroGerm : Type := meroGermSubring

instance : CommRing MeroGerm := inferInstanceAs (CommRing meroGermSubring)

theorem isField_meroGerm : IsField MeroGerm := by
  refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h
    exact one_ne_zero_meroGerm (congrArg Subtype.val h).symm
  · intro x hne
    have hne' : (show (meroGermSubring : Type) from x).1 ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨h, hh, hgh⟩ := exists_inv_meroGerm (show (meroGermSubring : Type) from x).2 hne'
    exact ⟨show MeroGerm from ⟨h, hh⟩, Subtype.ext hgh⟩

instance : Field MeroGerm := isField_meroGerm.toField

/-- The germ underlying an element. -/
def MeroGerm.germ (x : MeroGerm) : Germ (𝓝[≠] (0 : ℂ)) ℂ :=
  (show (meroGermSubring : Type) from x).1

theorem MeroGerm.germ_injective : Function.Injective MeroGerm.germ := fun _ _ h => Subtype.ext h

/-- The germ of a function meromorphic at the origin. -/
def ofMero (f : ℂ → ℂ) (hf : MeromorphicAt f 0) : MeroGerm :=
  show MeroGerm from ⟨(f : Germ (𝓝[≠] (0 : ℂ)) ℂ), ⟨f, hf, rfl⟩⟩

@[simp] theorem germ_ofMero (f : ℂ → ℂ) (hf : MeromorphicAt f 0) :
    (ofMero f hf).germ = (f : Germ (𝓝[≠] (0 : ℂ)) ℂ) := rfl

theorem ofMero_eq_iff {f g : ℂ → ℂ} (hf : MeromorphicAt f 0) (hg : MeromorphicAt g 0) :
    ofMero f hf = ofMero g hg ↔ f =ᶠ[𝓝[≠] (0 : ℂ)] g := by
  constructor
  · intro h
    have := congrArg MeroGerm.germ h
    rw [germ_ofMero, germ_ofMero] at this
    exact Germ.coe_eq.mp this
  · intro h
    exact MeroGerm.germ_injective (by rw [germ_ofMero, germ_ofMero]; exact Germ.coe_eq.mpr h)

theorem ofMero_add {f g : ℂ → ℂ} (hf : MeromorphicAt f 0) (hg : MeromorphicAt g 0) :
    ofMero f hf + ofMero g hg = ofMero (f + g) (hf.add hg) := rfl

theorem ofMero_mul {f g : ℂ → ℂ} (hf : MeromorphicAt f 0) (hg : MeromorphicAt g 0) :
    ofMero f hf * ofMero g hg = ofMero (f * g) (hf.mul hg) := rfl

theorem ofMero_neg {f : ℂ → ℂ} (hf : MeromorphicAt f 0) : -ofMero f hf = ofMero (-f) hf.neg := rfl

theorem ofMero_sub {f g : ℂ → ℂ} (hf : MeromorphicAt f 0) (hg : MeromorphicAt g 0) :
    ofMero f hf - ofMero g hg = ofMero (f - g) (hf.sub hg) := by
  rw [sub_eq_add_neg, ofMero_neg, ofMero_add]
  exact (ofMero_eq_iff _ _).mpr (Eventually.of_forall fun z => by simp [sub_eq_add_neg])

theorem ofMero_zero : ofMero (fun _ => 0) (MeromorphicAt.const 0 0) = 0 := rfl

theorem ofMero_one : ofMero (fun _ => 1) (MeromorphicAt.const 1 0) = 1 := rfl

theorem ofMero_eq_zero_iff {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    ofMero f hf = 0 ↔ f =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 := by
  rw [← ofMero_zero]
  exact ofMero_eq_iff hf _

theorem ofMero_inv {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    (ofMero f hf)⁻¹ = ofMero f⁻¹ hf.inv := by
  by_cases h : ofMero f hf = 0
  · rw [h, inv_zero, eq_comm, ofMero_eq_zero_iff]
    have h0 := (ofMero_eq_zero_iff hf).mp h
    exact h0.mono fun z hz => by simp [hz]
  · apply inv_eq_of_mul_eq_one_right
    rw [ofMero_mul, ← ofMero_one, ofMero_eq_iff]
    have hnetop : meromorphicOrderAt f 0 ≠ ⊤ := by
      intro htop
      exact h ((ofMero_eq_zero_iff hf).mpr (meromorphicOrderAt_eq_top_iff.mp htop))
    have hev := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp hnetop
    exact hev.mono fun z hz => by simp [hz]

theorem ofMero_congr {f g : ℂ → ℂ} (hf : MeromorphicAt f 0) (hfg : f = g) :
    ofMero f hf = ofMero g (hfg ▸ hf) := by
  subst hfg
  rfl

/-- Every element is the germ of a meromorphic function. -/
theorem MeroGerm.exists_rep (x : MeroGerm) :
    ∃ (f : ℂ → ℂ) (hf : MeromorphicAt f 0), x = ofMero f hf := by
  obtain ⟨f, hf, hcoe⟩ := (show (meroGermSubring : Type) from x).2
  exact ⟨f, hf, MeroGerm.germ_injective (by rw [germ_ofMero]; exact hcoe.symm)⟩

/-- A chosen representative. -/
def MeroGerm.rep (x : MeroGerm) : ℂ → ℂ := Classical.choose x.exists_rep

theorem MeroGerm.rep_mero (x : MeroGerm) : MeromorphicAt x.rep 0 :=
  (Classical.choose_spec x.exists_rep).choose

theorem MeroGerm.ofMero_rep (x : MeroGerm) : ofMero x.rep x.rep_mero = x :=
  ((Classical.choose_spec x.exists_rep).choose_spec).symm

theorem MeroGerm.rep_ofMero {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    (ofMero f hf).rep =ᶠ[𝓝[≠] (0 : ℂ)] f :=
  (ofMero_eq_iff (ofMero f hf).rep_mero hf).mp (ofMero f hf).ofMero_rep

/-! ### The derivation -/

/-- Functions agreeing off the origin have derivatives agreeing off the origin. -/
theorem deriv_eventuallyEq_nhdsNE {f g : ℂ → ℂ} (h : f =ᶠ[𝓝[≠] (0 : ℂ)] g) :
    deriv f =ᶠ[𝓝[≠] (0 : ℂ)] deriv g := by
  obtain ⟨u, hu, h0u, hsub⟩ := mem_nhdsWithin.mp h
  filter_upwards [inter_mem_nhdsWithin ({0}ᶜ : Set ℂ) (hu.mem_nhds h0u)] with z hz
  have hmem : u ∩ {0}ᶜ ∈ 𝓝 z := (hu.inter isOpen_compl_singleton).mem_nhds ⟨hz.2, hz.1⟩
  exact Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset hmem hsub)

/-- The derivative of a meromorphic germ. -/
def meroDeriv (x : MeroGerm) : MeroGerm := ofMero (deriv x.rep) x.rep_mero.deriv

theorem meroDeriv_ofMero {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    meroDeriv (ofMero f hf) = ofMero (deriv f) hf.deriv :=
  (ofMero_eq_iff _ _).mpr (deriv_eventuallyEq_nhdsNE (MeroGerm.rep_ofMero hf))

theorem meroDeriv_add (x y : MeroGerm) : meroDeriv (x + y) = meroDeriv x + meroDeriv y := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [ofMero_add, meroDeriv_ofMero, meroDeriv_ofMero, meroDeriv_ofMero, ofMero_add, ofMero_eq_iff]
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
  exact deriv_add hfz.differentiableAt hgz.differentiableAt

theorem meroDeriv_mul (x y : MeroGerm) :
    meroDeriv (x * y) = x * meroDeriv y + y * meroDeriv x := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [ofMero_mul, meroDeriv_ofMero, meroDeriv_ofMero, meroDeriv_ofMero, ofMero_mul, ofMero_mul,
    ofMero_add, ofMero_eq_iff]
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hfz hgz
  rw [deriv_mul hfz.differentiableAt hgz.differentiableAt]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

theorem meroDeriv_zero : meroDeriv 0 = 0 := by
  rw [← ofMero_zero, meroDeriv_ofMero, ofMero_eq_iff]
  exact Eventually.of_forall fun z => by simp

/-- **The derivation of the meromorphic germ field.** -/
def meroGermDerivation : Derivation ℤ MeroGerm MeroGerm :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap ⟨⟨meroDeriv, meroDeriv_zero⟩, meroDeriv_add⟩)
    fun a b => by
      show meroDeriv (a * b) = a • meroDeriv b + b • meroDeriv a
      rw [meroDeriv_mul, smul_eq_mul, smul_eq_mul]

instance : Differential MeroGerm := ⟨meroGermDerivation⟩

theorem meroGerm_deriv_apply (x : MeroGerm) : Differential.deriv x = meroDeriv x := rfl

/-! ### Constants, the coordinate, and rational functions -/

/-- The constant germs. -/
def constGerm : ℂ →+* MeroGerm where
  toFun c := ofMero (fun _ => c) (MeromorphicAt.const c 0)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Algebra ℂ MeroGerm := constGerm.toAlgebra

theorem algebraMap_complex_meroGerm (c : ℂ) :
    algebraMap ℂ MeroGerm c = ofMero (fun _ => c) (MeromorphicAt.const c 0) := rfl

/-- The coordinate germ. -/
def zGerm : MeroGerm := ofMero id analyticAt_id.meromorphicAt

theorem polynomial_meromorphicAt (p : ℂ[X]) : MeromorphicAt (fun z => p.eval z) 0 :=
  (Differentiable.analyticAt (fun _ => p.differentiableAt) 0).meromorphicAt

/-- **Polynomials evaluate at the coordinate to their value germs.** -/
theorem aeval_zGerm (p : ℂ[X]) :
    Polynomial.aeval zGerm p = ofMero (fun z => p.eval z) (polynomial_meromorphicAt p) := by
  induction p using Polynomial.induction_on with
  | C a =>
      rw [aeval_C, algebraMap_complex_meroGerm, ofMero_eq_iff]
      exact Eventually.of_forall fun _ => by simp
  | add p q hp hq =>
      rw [map_add, hp, hq, ofMero_add]
      exact (ofMero_eq_iff _ _).mpr (Eventually.of_forall fun z => by simp)
  | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul, ih, aeval_X, zGerm, ofMero_mul]
      exact (ofMero_eq_iff _ _).mpr (Eventually.of_forall fun z => by simp [mul_assoc])

/-- A nonzero polynomial is eventually nonzero off the origin. -/
theorem eventually_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), p.eval z ≠ 0 := by
  classical
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ r ∈ p.roots.toFinset, z ≠ r := by
    rw [eventually_all_finset]
    intro r _
    by_cases hr : r = 0
    · subst hr
      exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (Ne.symm hr))
  filter_upwards [hall] with z hz hzero
  exact hz z (Multiset.mem_toFinset.mpr ((mem_roots hp).mpr hzero)) rfl

theorem aeval_zGerm_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : Polynomial.aeval zGerm p ≠ 0 := by
  rw [aeval_zGerm, Ne, ofMero_eq_zero_iff]
  intro h
  obtain ⟨z, hz1, hz2⟩ := ((eventually_eval_ne_zero hp).and h).exists
  exact hz1 hz2

/-- **The rational function field inside the germ field.** -/
def ratGerm : RatFunc ℂ →+* MeroGerm :=
  RatFunc.liftRingHom (Polynomial.aeval zGerm).toRingHom fun _ hp =>
    mem_nonZeroDivisors_of_ne_zero (aeval_zGerm_ne_zero (nonZeroDivisors.ne_zero hp))

instance : Algebra (RatFunc ℂ) MeroGerm := ratGerm.toAlgebra

theorem ratValue_meromorphicAt (Q : RatFunc ℂ) : MeromorphicAt (fun z => ratValue Q z) 0 := by
  have h := (polynomial_meromorphicAt Q.num).mul (polynomial_meromorphicAt Q.denom).inv
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp [ratValue, div_eq_mul_inv]

/-- **A rational function goes to the germ of its values.** -/
theorem algebraMap_ratFunc_meroGerm (Q : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) MeroGerm Q
      = ofMero (fun z => ratValue Q z) (ratValue_meromorphicAt Q) := by
  show ratGerm Q = _
  rw [ratGerm, RatFunc.liftRingHom_apply]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [aeval_zGerm, aeval_zGerm, div_eq_mul_inv, ofMero_inv, ofMero_mul, ofMero_eq_iff]
  exact Eventually.of_forall fun z => by simp [ratValue, div_eq_mul_inv]

instance : IsScalarTower ℂ (RatFunc ℂ) MeroGerm := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [algebraMap_ratFunc_meroGerm, algebraMap_complex_meroGerm, ofMero_eq_iff]
  refine Eventually.of_forall fun z => ?_
  show c = ratValue (algebraMap ℂ (RatFunc ℂ) c) z
  rw [RatFunc.algebraMap_eq_C, ratValue_C]

theorem algebraMap_X_meroGerm : algebraMap (RatFunc ℂ) MeroGerm RatFunc.X = zGerm := by
  rw [algebraMap_ratFunc_meroGerm, zGerm, ofMero_eq_iff]
  exact Eventually.of_forall fun z => by simp [ratValue]

/-! ### Rational derivatives are analytic derivatives -/

/-- The value of a quotient of polynomials where its denominator does not vanish. -/
theorem ratValue_div_algebraMap {A B : ℂ[X]} {z : ℂ} (hB : B.eval z ≠ 0) :
    ratValue (algebraMap ℂ[X] (RatFunc ℂ) A / algebraMap ℂ[X] (RatFunc ℂ) B) z
      = A.eval z / B.eval z := by
  set f := algebraMap ℂ[X] (RatFunc ℂ) A / algebraMap ℂ[X] (RatFunc ℂ) B with hf
  have hdvd := RatFunc.denom_div_dvd A B
  have hden : f.denom.eval z ≠ 0 := by
    obtain ⟨c, hc⟩ := hdvd
    intro h0
    apply hB
    rw [hc, eval_mul, h0, zero_mul]
  have hB0 : B ≠ 0 := fun h => hB (by rw [h, eval_zero])
  have hBf : algebraMap ℂ[X] (RatFunc ℂ) B ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr hB0
  have hcross : f.num * B = A * f.denom := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul, map_mul, algebraMap_num_eq, hf]
    field_simp
  have hev := congrArg (Polynomial.eval z) hcross
  rw [eval_mul, eval_mul] at hev
  rw [ratValue]
  field_simp
  linear_combination hev

/-- **The derivative of the value function is the value function of the derivative.** -/
theorem hasDerivAt_ratValue {Q : RatFunc ℂ} {z : ℂ} (hz : Q.denom.eval z ≠ 0) :
    HasDerivAt (fun w => ratValue Q w) (ratValue (ratFuncDeriv Q) z) z := by
  have hD := RatFunc.denom_ne_zero Q
  have hDf : algebraMap ℂ[X] (RatFunc ℂ) Q.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr hD
  have hQ : ratFuncDeriv Q = algebraMap ℂ[X] (RatFunc ℂ)
        (derivative Q.num * Q.denom - Q.num * derivative Q.denom)
      / algebraMap ℂ[X] (RatFunc ℂ) (Q.denom ^ 2) := by
    conv_lhs => rw [← RatFunc.num_div_denom Q]
    rw [ratFuncDeriv_div_general hDf, ratFuncDeriv_algebraMap, ratFuncDeriv_algebraMap, map_sub,
      map_mul, map_mul, map_pow]
  have hz2 : (Q.denom ^ 2).eval z ≠ 0 := by rw [eval_pow]; exact pow_ne_zero 2 hz
  rw [hQ, ratValue_div_algebraMap hz2, eval_sub, eval_mul, eval_mul, eval_pow]
  have h := (Q.num.hasDerivAt z).div (Q.denom.hasDerivAt z) hz
  exact h

theorem eventually_denom_eval_ne_zero_nhdsNE (Q : RatFunc ℂ) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), Q.denom.eval z ≠ 0 :=
  eventually_eval_ne_zero (RatFunc.denom_ne_zero Q)

/-- **The embedding of `ℂ(z)` is differential.** -/
theorem meroDeriv_algebraMap (Q : RatFunc ℂ) :
    meroDeriv (algebraMap (RatFunc ℂ) MeroGerm Q)
      = algebraMap (RatFunc ℂ) MeroGerm (ratFuncDeriv Q) := by
  rw [algebraMap_ratFunc_meroGerm, algebraMap_ratFunc_meroGerm, meroDeriv_ofMero, ofMero_eq_iff]
  filter_upwards [eventually_denom_eval_ne_zero_nhdsNE Q] with z hz
  exact (hasDerivAt_ratValue hz).deriv

/-! ### Pullback along an analytic map fixing the origin -/

variable {g : ℂ → ℂ}

/-- A map analytic at the origin, fixing it, with nonzero derivative, keeps the punctured
neighbourhood filter. -/
theorem tendsto_nhdsNE_of_deriv_ne_zero (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hgd : deriv g 0 ≠ 0) : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have := hg.continuousAt.tendsto
    rw [hg0] at this
    exact this.mono_left nhdsWithin_le_nhds
  · rcases hg.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hd : deriv g 0 = deriv (fun _ : ℂ => (0 : ℂ)) 0 := Filter.EventuallyEq.deriv_eq h
      rw [deriv_const] at hd
      exact hgd hd
    · exact h.mono fun z hz => hz

/-- **Precomposition with a map fixing the origin.** -/
def meroPull (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (x : MeroGerm) : MeroGerm :=
  ofMero (x.rep ∘ g) (by
    have h := x.rep_mero
    rw [← hg0] at h
    exact h.comp_analyticAt hg)

theorem meroPull_ofMero (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (hgd : deriv g 0 ≠ 0)
    {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    meroPull hg hg0 (ofMero f hf)
      = ofMero (f ∘ g) (by rw [← hg0] at hf; exact hf.comp_analyticAt hg) :=
  (ofMero_eq_iff _ _).mpr ((tendsto_nhdsNE_of_deriv_ne_zero hg hg0 hgd).eventually
    (MeroGerm.rep_ofMero hf))

/-- **Precomposition is a ring endomorphism.** -/
def meroPullHom (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (hgd : deriv g 0 ≠ 0) :
    MeroGerm →+* MeroGerm where
  toFun := meroPull hg hg0
  map_one' := by rw [← ofMero_one, meroPull_ofMero hg hg0 hgd]; rfl
  map_mul' x y := by
    obtain ⟨f, hf, rfl⟩ := x.exists_rep
    obtain ⟨f', hf', rfl⟩ := y.exists_rep
    rw [ofMero_mul, meroPull_ofMero hg hg0 hgd, meroPull_ofMero hg hg0 hgd,
      meroPull_ofMero hg hg0 hgd, ofMero_mul]
    rfl
  map_zero' := by rw [← ofMero_zero, meroPull_ofMero hg hg0 hgd]; rfl
  map_add' x y := by
    obtain ⟨f, hf, rfl⟩ := x.exists_rep
    obtain ⟨f', hf', rfl⟩ := y.exists_rep
    rw [ofMero_add, meroPull_ofMero hg hg0 hgd, meroPull_ofMero hg hg0 hgd,
      meroPull_ofMero hg hg0 hgd, ofMero_add]
    rfl

theorem meroPullHom_ofMero (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (hgd : deriv g 0 ≠ 0)
    {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    meroPullHom hg hg0 hgd (ofMero f hf)
      = ofMero (f ∘ g) (by rw [← hg0] at hf; exact hf.comp_analyticAt hg) :=
  meroPull_ofMero hg hg0 hgd hf

/-- **The chain rule for precomposition.** -/
theorem meroDeriv_meroPullHom (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (hgd : deriv g 0 ≠ 0)
    (x : MeroGerm) :
    meroDeriv (meroPullHom hg hg0 hgd x)
      = ofMero (deriv g) hg.deriv.meromorphicAt * meroPullHom hg hg0 hgd (meroDeriv x) := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [meroPullHom_ofMero, meroDeriv_ofMero, meroDeriv_ofMero, meroPullHom_ofMero, ofMero_mul,
    ofMero_eq_iff]
  have htend := tendsto_nhdsNE_of_deriv_ne_zero hg hg0 hgd
  have hgan : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ g z := hg.eventually_analyticAt
  filter_upwards [htend.eventually hf.eventually_analyticAt, nhdsWithin_le_nhds hgan]
    with z hfz hgz
  rw [deriv_comp z hfz.differentiableAt hgz.differentiableAt]
  simp only [Pi.mul_apply, Function.comp_apply]
  ring

end

end GaloisForLFunctions.HTGeometry
