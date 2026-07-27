import GaloisForLFunctions.HTGeometry.OrbitQuotientLiftNoGo

/-!
# A weight restores the invariant vector that the unweighted completion destroys

`OrbitQuotientLiftNoGo` proves that a square-summable regular vector invariant under an infinite
subgroup is zero: in `ℓ²(G)` the invariants of an infinite subgroup are `{0}`, so the object one
wants to construct is not merely small in the completion — it is absent from it.

That obstruction is an artifact of the *unweighted* norm, and this file says exactly when it
disappears.  For a weight `w : G → ℝ` the invariants of the weighted completion are governed by a
single scalar per orbit, the pushforward weight

`W(H·x) = ∑_(h ∈ H) w(h · x)`,

and the dichotomy is sharp:

* if a nonzero invariant vector is weighted square-summable, then `W(H·x) < ∞` at every point where
  it does not vanish (`summable_weight_orbit_of_invariant`);
* conversely, `W(H·x) < ∞` for a single orbit already produces one — the indicator of that orbit
  (`exists_nonzero_invariant_of_summable_weight_orbit`).

Taking `w ≡ 1` recovers the no-go, since `∑_(h ∈ H) 1` diverges for infinite `H`
(`eq_zero_of_infinite_subgroup_invariant_unweighted`).  So the prescription "form the nuclear
object before Hilbert completion" has a quantitative counterpart: complete against a weight that is
summable along the orbits, and the invariants survive.
-/

namespace GaloisForLFunctions

noncomputable section

variable {G E : Type*} [Group G] [NormedAddCommGroup E]

/-- The orbit of `x` under `H`, as a set. -/
def subgroupOrbit (H : Subgroup G) (x : G) : Set G :=
  {g : G | ∃ h : H, g = h.1 * x}

theorem mem_subgroupOrbit_self (H : Subgroup G) (x : G) : x ∈ subgroupOrbit H x :=
  ⟨1, by simp⟩

theorem subgroupOrbit_smul_mem {H : Subgroup G} {x g : G} (h : H)
    (hg : g ∈ subgroupOrbit H x) : h.1 * g ∈ subgroupOrbit H x := by
  obtain ⟨k, rfl⟩ := hg
  exact ⟨h * k, by rw [Subgroup.coe_mul, mul_assoc]⟩

theorem subgroupOrbit_of_smul_mem {H : Subgroup G} {x g : G} (h : H)
    (hg : h.1 * g ∈ subgroupOrbit H x) : g ∈ subgroupOrbit H x := by
  obtain ⟨k, hk⟩ := hg
  refine ⟨h⁻¹ * k, ?_⟩
  have : g = h.1⁻¹ * (h.1 * g) := by group
  rw [this, hk, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc]

/-- Orbit parametrization is injective: `h ↦ h · x` never repeats. -/
theorem orbitParam_injective (H : Subgroup G) (x : G) :
    Function.Injective (fun h : H => h.1 * x) := by
  intro h k hEq
  exact Subtype.ext (mul_right_cancel hEq)

/-- **Necessity.**  A weighted square-summable invariant vector forces the weight to be summable
along the orbit through every point at which the vector does not vanish. -/
theorem summable_weight_orbit_of_invariant
    (H : Subgroup G) (w : G → ℝ) (f : G → E)
    (hsum : Summable fun g => w g * ‖f g‖ ^ 2)
    (hinv : ∀ h : H, ∀ y, f (h.1 * y) = f y)
    {x : G} (hx : f x ≠ 0) :
    Summable fun h : H => w (h.1 * x) := by
  have hcomp : Summable fun h : H => w (h.1 * x) * ‖f (h.1 * x)‖ ^ 2 :=
    hsum.comp_injective (orbitParam_injective H x)
  have hrw : (fun h : H => w (h.1 * x) * ‖f (h.1 * x)‖ ^ 2)
      = fun h : H => w (h.1 * x) * ‖f x‖ ^ 2 := by
    funext h
    rw [hinv h x]
  rw [hrw] at hcomp
  have hpos : (0 : ℝ) < ‖f x‖ ^ 2 := by positivity
  have := hcomp.div_const (‖f x‖ ^ 2)
  simpa [mul_div_assoc, div_self hpos.ne'] using this

/-- **Sufficiency.**  Summability of the weight along a single orbit produces a nonzero invariant
vector in the weighted completion: the indicator of that orbit. -/
theorem exists_nonzero_invariant_of_summable_weight_orbit
    (H : Subgroup G) (w : G → ℝ) (x : G) (v : E)
    (horb : Summable fun h : H => w (h.1 * x)) :
    ∃ f : G → E, f x = v ∧ (∀ h : H, ∀ y, f (h.1 * y) = f y)
      ∧ Summable fun g => w g * ‖f g‖ ^ 2 := by
  classical
  set S : Set G := subgroupOrbit H x with hS
  refine ⟨Set.indicator S (fun _ => v), ?_, ?_, ?_⟩
  · exact Set.indicator_of_mem (mem_subgroupOrbit_self H x) _
  · intro h y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (subgroupOrbit_smul_mem h hy)]
    · have hny : h.1 * y ∉ S := fun hmem => hy (subgroupOrbit_of_smul_mem h hmem)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hny]
  · have hfun : (fun g => w g * ‖Set.indicator S (fun _ => v) g‖ ^ 2)
        = Set.indicator S (fun g => w g * ‖v‖ ^ 2) := by
      funext g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
        simp
    rw [hfun, ← summable_subtype_iff_indicator]
    have hbij : Function.Bijective (fun h : H => (⟨h.1 * x, ⟨h, rfl⟩⟩ : S)) := by
      constructor
      · intro h k hEq
        exact orbitParam_injective H x (congrArg Subtype.val hEq)
      · rintro ⟨g, h, rfl⟩
        exact ⟨h, rfl⟩
    have hHsum : Summable fun h : H => w (h.1 * x) * ‖v‖ ^ 2 := horb.mul_right _
    exact ((Equiv.ofBijective _ hbij).summable_iff).mp hHsum

/-- The unweighted no-go is the case `w ≡ 1`: an infinite orbit cannot carry a summable constant
weight, so the invariants of the unweighted completion vanish. -/
theorem eq_zero_of_infinite_subgroup_invariant_unweighted
    (H : Subgroup G) [Infinite H] (f : G → E)
    (hsum : Summable fun g => ‖f g‖ ^ 2)
    (hinv : ∀ h : H, ∀ y, f (h.1 * y) = f y) :
    f = 0 := by
  funext x
  by_contra hx
  have hsum' : Summable fun g => (1 : ℝ) * ‖f g‖ ^ 2 := by simpa using hsum
  have hone : Summable fun _ : H => (1 : ℝ) :=
    summable_weight_orbit_of_invariant H (fun _ => (1 : ℝ)) f hsum' hinv hx
  have htend := hone.tendsto_cofinite_zero
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds htend
  exact one_ne_zero this

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

open Filter

variable {G E : Type*} [Group G] [NormedAddCommGroup E]

/-! ## The trade, quantified

`summable_weight_orbit_of_invariant` says the invariants of a weighted completion exist only when the
weight is summable along the orbit.  Summability is not a neutral condition: it bounds *block size
times least weight* by the block's total weight, and the totals of disjoint blocks tend to zero.  So
a weighted completion that admits the invariant object cannot also assign uniformly non-negligible
weight to blocks of growing size — existence of the object and uniform sensitivity along the orbit
are incompatible, and the incompatibility is quantitative in the block size.
-/

/-- Block size times the least weight in the block is at most the block's total weight. -/
theorem card_mul_orbit_weight_inf_le
    (H : Subgroup G) (w : G → ℝ) (x : G) (F : Finset H) (hF : F.Nonempty) :
    (F.card : ℝ) * F.inf' hF (fun h => w (h.1 * x)) ≤ ∑ h ∈ F, w (h.1 * x) := by
  have hle : ∀ h ∈ F, F.inf' hF (fun k => w (k.1 * x)) ≤ w (h.1 * x) :=
    fun h hh => Finset.inf'_le _ hh
  calc (F.card : ℝ) * F.inf' hF (fun h => w (h.1 * x))
      = ∑ _h ∈ F, F.inf' hF (fun k => w (k.1 * x)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ h ∈ F, w (h.1 * x) := Finset.sum_le_sum hle

/-- The weight mass outside a finite block tends to zero along the finite blocks. -/
theorem tendsto_orbitTailWeight_zero
    (H : Subgroup G) (w : G → ℝ) (x : G) :
    Tendsto (fun F : Finset H => ∑' h : {k : H // k ∉ F}, w (h.1.1 * x)) atTop (nhds 0) :=
  tendsto_tsum_compl_atTop_zero (fun h : H => w (h.1 * x))

/-- **Existence of the invariant object forbids uniform sensitivity along the orbit.**  If a nonzero
`H`-invariant vector is weighted square-summable, then for every `ε > 0` there is a finite set of the
period group outside of which every finite block satisfies `card · (least weight) ≤ ε`.  Uniform
weight on blocks of unbounded size is therefore impossible. -/
theorem exists_finset_card_mul_inf_le_of_invariant
    (H : Subgroup G) (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (f : G → E)
    (hsum : Summable fun g => w g * ‖f g‖ ^ 2)
    (hinv : ∀ h : H, ∀ y, f (h.1 * y) = f y)
    {x : G} (hx : f x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ F₀ : Finset H, ∀ F : Finset H, ∀ hF : F.Nonempty, Disjoint F F₀ →
      (F.card : ℝ) * F.inf' hF (fun h => w (h.1 * x)) ≤ ε := by
  have horb : Summable fun h : H => w (h.1 * x) :=
    summable_weight_orbit_of_invariant H w f hsum hinv hx
  have htail := tendsto_orbitTailWeight_zero H w x
  obtain ⟨F₀, hF₀⟩ := (htail.eventually (eventually_le_nhds hε)).exists
  refine ⟨F₀, ?_⟩
  intro F hF hdisj
  refine (card_mul_orbit_weight_inf_le H w x F hF).trans ?_
  have hsubset : ∀ h ∈ F, h ∉ F₀ := fun h hh => Finset.disjoint_left.mp hdisj hh
  have hsum_le : (∑ h ∈ F, w (h.1 * x))
      ≤ ∑' h : {k : H // k ∉ F₀}, w (h.1.1 * x) := by
    classical
    have hcompl : Summable fun h : {k : H // k ∉ F₀} => w (h.1.1 * x) := horb.subtype _
    let emb : {k : H // k ∈ F} ↪ {k : H // k ∉ F₀} :=
      ⟨fun h => ⟨h.1, hsubset h.1 h.2⟩, by
        intro a b hab
        exact Subtype.ext (congrArg (fun z : {k : H // k ∉ F₀} => (z : H)) hab)⟩
    have hmap : ∑ h ∈ F.attach.map emb, w (h.1.1 * x) = ∑ h ∈ F, w (h.1 * x) := by
      rw [Finset.sum_map]
      exact Finset.sum_attach F (fun h => w (h.1 * x))
    have hsub := hcompl.sum_le_tsum (F.attach.map emb) (fun i _ => hw _)
    rw [hmap] at hsub
    exact hsub
  exact hsum_le.trans hF₀

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

variable {G E : Type*} [Group G] [NormedAddCommGroup E]

/-! ## Equivariance forces the abscissa

A completion that carries the group action cannot use an arbitrary weight: the weight must be
quasi-invariant, `w(h · g) = chi(h) · w(g)` for a multiplier `chi` on the period subgroup.  For such
a weight the orbit sums collapse to a single scalar series, so **whether the invariant object exists
is a property of the multiplier alone** — it is intrinsic to the action, not a modelling choice.
-/

/-- For a quasi-invariant weight the orbit sum is the multiplier series scaled by `w x`. -/
theorem orbitWeight_of_quasiInvariant
    (H : Subgroup G) (w : G → ℝ) (chi : H → ℝ)
    (hquasi : ∀ (h : H) (g : G), w (h.1 * g) = chi h * w g) (x : G) :
    (fun h : H => w (h.1 * x)) = fun h : H => chi h * w x :=
  funext fun h => hquasi h x

/-- Orbit-summability of a quasi-invariant weight is summability of its multiplier. -/
theorem summable_orbitWeight_iff_summable_multiplier
    (H : Subgroup G) (w : G → ℝ) (chi : H → ℝ)
    (hquasi : ∀ (h : H) (g : G), w (h.1 * g) = chi h * w g) {x : G} (hwx : w x ≠ 0) :
    (Summable fun h : H => w (h.1 * x)) ↔ Summable chi := by
  rw [orbitWeight_of_quasiInvariant H w chi hquasi x]
  constructor
  · intro hs
    have := hs.mul_right (w x)⁻¹
    refine this.congr fun h => ?_
    field_simp
  · intro hs
    exact hs.mul_right (w x)

/-- **The admissible range is intrinsic.**  For a quasi-invariant weight, a nonzero invariant vector
of the weighted completion exists exactly when the multiplier character is summable over the period
subgroup.  No choice of base point and no rescaling of the weight can change this: the abscissa of
convergence of the multiplier is a property of the action. -/
theorem exists_nonzero_invariant_iff_summable_multiplier
    (H : Subgroup G) (w : G → ℝ) (chi : H → ℝ)
    (hquasi : ∀ (h : H) (g : G), w (h.1 * g) = chi h * w g)
    {x : G} (hwx : w x ≠ 0) {v : E} (hv : v ≠ 0) :
    Summable chi ↔
      ∃ f : G → E, f x = v ∧ (∀ h : H, ∀ y, f (h.1 * y) = f y)
        ∧ Summable fun g => w g * ‖f g‖ ^ 2 := by
  constructor
  · intro hchi
    exact exists_nonzero_invariant_of_summable_weight_orbit H w x v
      ((summable_orbitWeight_iff_summable_multiplier H w chi hquasi hwx).mpr hchi)
  · rintro ⟨f, hfx, hinv, hsum⟩
    refine (summable_orbitWeight_iff_summable_multiplier H w chi hquasi hwx).mp ?_
    exact summable_weight_orbit_of_invariant H w f hsum hinv (by rw [hfx]; exact hv)

end

end GaloisForLFunctions
