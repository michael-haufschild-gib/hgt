import GaloisForLFunctions.HTGeometry.HullChartFrequencyRank
import GaloisForLFunctions.HTGeometry.RelativeFrequencyDual

/-!
# The relative frequency rank of a phase carrier

A parameter subgroup of the carrier is built from any `ℚ`-linear functional package sending a
frequency packet to the standard basis of `ℝ^r`.  If the package is chosen to kill a rational
subspace of frequencies, the parameter subgroup lands in the *kernel* of the restriction of
characters to that subspace — the carrier's fibre over the coefficient carrier.

Charts injective only on that fibre therefore bound the rank of the frequency group *relative to*
the subgroup, with no bound on the subgroup itself.  This is the mechanism that makes an infinite
dimensional coefficient carrier harmless.
-/

namespace GaloisForLFunctions

open Metric Set

open scoped BoundedContinuousFunction

variable {V : Type*} [NormedAddCommGroup V] {f : ℝ →ᵇ V}

/-- **The carrier's parameter subgroup attached to a `ℚ`-linear coordinate package.** -/
theorem exists_continuous_hullParameter_of_dual (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {r : ℕ} (v : ℝ →ₗ[ℚ] (Fin r → ℝ)) :
    ∃ φ : (Fin r → ℝ) → BohrHull f, Continuous φ ∧
      ∀ (t : Fin r → ℝ) (γ : ℝ), IsBohrHullFrequency f γ →
        bohrHullChar f γ (φ t) = Complex.exp (((∑ j, v γ j * t j : ℝ) : ℂ) * Complex.I) := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  set ω : (Fin r → ℝ) → ℝ → ℂ :=
    fun t γ => Complex.exp (((∑ j, v γ j * t j : ℝ) : ℂ) * Complex.I) with hωdef
  have hmul : ∀ t a b, ω t (a + b) = ω t a * ω t b := by
    intro t a b
    rw [hωdef]
    simp only [map_add, Pi.add_apply]
    rw [← Complex.exp_add, ← add_mul]
    congr 2
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hnorm : ∀ t a, ‖ω t a‖ = 1 := by
    intro t a
    rw [hωdef]
    simp [Complex.norm_exp]
  choose φ hφ using fun t => exists_bohrHull_char_eq htb (hmul t) (hnorm t)
  refine ⟨φ, ?_, hφ⟩
  set E : BohrHull f → (bohrHullFrequencies f → ℂ) :=
    fun x γ => bohrHullChar f (γ : ℝ) x with hEdef
  have hEcont : Continuous E := continuous_pi fun γ => continuous_bohrHullChar f _
  have hEinj : Function.Injective E := by
    intro x y hxy
    refine bohrHullChar_separates hf htb ?_
    intro mu hmu
    exact congrFun hxy ⟨mu, mem_bohrHullFrequencies.mpr hmu⟩
  have hbij : Function.Bijective (fun x : BohrHull f => (⟨E x, ⟨x, rfl⟩⟩ : Set.range E)) := by
    constructor
    · intro a b hab
      exact hEinj (congrArg Subtype.val hab)
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  set e : BohrHull f ≃ₜ Set.range E :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij) (hEcont.subtype_mk _)
    with hedef
  have hEφ : Continuous (fun t => E (φ t)) := by
    have hrw : (fun t => E (φ t)) = fun t => fun γ : bohrHullFrequencies f => ω t (γ : ℝ) := by
      funext t γ
      exact hφ t (γ : ℝ) (mem_bohrHullFrequencies.mp γ.2)
    rw [hrw, hωdef]
    refine continuous_pi fun γ => ?_
    refine Complex.continuous_exp.comp ?_
    refine Continuous.mul ?_ continuous_const
    refine Complex.continuous_ofReal.comp ?_
    exact continuous_finsetSum _ fun j _ => (continuous_apply j).const_smul (v (γ : ℝ) j) |>.congr
      (fun t => by simp [smul_eq_mul])
  have hφeq : φ = fun t => (e.symm ⟨E (φ t), ⟨φ t, rfl⟩⟩ : BohrHull f) := by
    funext t
    have hex : e (φ t) = ⟨E (φ t), ⟨φ t, rfl⟩⟩ := rfl
    rw [← hex, e.symm_apply_apply]
  rw [hφeq]
  exact e.symm.continuous.comp (hEφ.subtype_mk _)

/-- The fibre of the carrier over the base point of the coefficient carrier: the points at which
every character coming from the subspace `W` is trivial. -/
def bohrHullKernel (f : ℝ →ᵇ V) (W : Submodule ℚ ℝ) : Set (BohrHull f) :=
  {x | ∀ μ : ℝ, IsBohrHullFrequency f μ → μ ∈ W → bohrHullChar f μ x = 1}

/-- **The relative parameter subgroup lies in the fibre.** -/
theorem exists_continuous_hullParameter_rel (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {r : ℕ} {lam : Fin r → ℝ} (W : Submodule ℚ ℝ)
    (hind : LinearIndependent ℚ fun j => W.mkQ (lam j))
    (hlam : ∀ j, IsBohrHullFrequency f (lam j)) :
    ∃ φ : (Fin r → ℝ) → BohrHull f, Continuous φ ∧
      (∀ (t : Fin r → ℝ) (j : Fin r),
        bohrHullChar f (lam j) (φ t) = Complex.exp ((t j : ℂ) * Complex.I)) ∧
      ∀ t : Fin r → ℝ, φ t ∈ bohrHullKernel f W := by
  classical
  obtain ⟨v, hvW, hvlam⟩ := HTGeometry.exists_rat_linear_dual_rel W hind
  obtain ⟨φ, hφcont, hφval⟩ := exists_continuous_hullParameter_of_dual hf htb v
  refine ⟨φ, hφcont, fun t j => ?_, fun t μ hμ hμW => ?_⟩
  · have hsum : (∑ i, v (lam j) i * t i) = t j := by
      rw [hvlam j]
      have hterm : ∀ i : Fin r, (Pi.single j (1 : ℝ) : Fin r → ℝ) i * t i
          = if i = j then t i else 0 := by
        intro i
        by_cases h : i = j <;> simp [h]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ j t]
      simp
    rw [hφval t (lam j) (hlam j), hsum]
  · have hzero : (∑ i, v μ i * t i) = 0 := by
      rw [hvW μ hμW]
      simp
    rw [hφval t μ hμ, hzero]
    simp

/-- **The relative frequency-rank bound from a chart atlas.**  Charts injective only on the fibre
bound the size of a frequency packet independent modulo the subspace. -/
theorem card_le_of_hull_charts_rel (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {r : ℕ} {lam : Fin r → ℝ} (W : Submodule ℚ ℝ)
    (hind : LinearIndependent ℚ fun j => W.mkQ (lam j))
    (hlam : ∀ j, IsBohrHullFrequency f (lam j))
    {N k : ℕ} (F : Fin N → Set (BohrHull f)) (hFclosed : ∀ j, IsClosed (F j))
    (hcover : ∀ x : BohrHull f, ∃ j, x ∈ F j)
    (E : Fin N → BohrHull f → EuclideanSpace ℝ (Fin k))
    (hEcont : ∀ j, ContinuousOn (E j) (F j))
    (hEinj : ∀ j, Set.InjOn (E j) (F j ∩ bohrHullKernel f W)) : r ≤ k := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  obtain ⟨φ, hφcont, hφval, hφker⟩ :=
    exists_continuous_hullParameter_rel hf htb W hind hlam
  set Ψ : EuclideanSpace ℝ (Fin r) → BohrHull f := fun v => φ fun j => Real.pi * v j with hΨ
  have hΨcont : Continuous Ψ := by
    refine hφcont.comp (continuous_pi fun j => ?_)
    exact continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  have hΨker : ∀ v, Ψ v ∈ bohrHullKernel f W := fun v => hφker _
  have hΨchar : ∀ v j, bohrHullChar f (lam j) (Ψ v)
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (v j : ℂ)) := by
    intro v j
    rw [hΨ, hφval]
    congr 1
    push_cast
    ring
  have hΨinj : Set.InjOn Ψ (unitCube r) := by
    intro v hv v' hv' heq
    refine HTGeometry.eq_of_exp_pi_mul_I_eq hv hv' fun j => ?_
    rw [← hΨchar v j, ← hΨchar v' j, heq]
  refine HTGeometry.le_of_unitCube_charts (fun j => Ψ ⁻¹' F j)
    (fun j => (hFclosed j).preimage hΨcont) (fun x _ => hcover (Ψ x))
    (fun j v => E j (Ψ v)) ?_ ?_
  · intro j
    exact (hEcont j).comp hΨcont.continuousOn fun v hv => hv.1
  · intro j v hv v' hv' heq
    exact hΨinj hv.2 hv'.2
      (hEinj j ⟨hv.1, hΨker v⟩ ⟨hv'.1, hΨker v'⟩ heq)

/-- **The relative bound in packet form.**  A frequency packet independent over `ℤ` modulo a
subgroup has at most `k` members, when the carrier has an atlas of `k`-dimensional charts injective
on the fibre over that subgroup. -/
theorem card_le_of_int_independent_mod (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (Γa : AddSubgroup ℝ) {r : ℕ} {lam : Fin r → ℝ}
    (hlam : ∀ j, IsBohrHullFrequency f (lam j))
    (hind : ∀ c : Fin r → ℤ, (∑ j, (c j : ℝ) * lam j) ∈ Γa → ∀ j, c j = 0)
    {N k : ℕ} (F : Fin N → Set (BohrHull f)) (hFclosed : ∀ j, IsClosed (F j))
    (hcover : ∀ x : BohrHull f, ∃ j, x ∈ F j)
    (E : Fin N → BohrHull f → EuclideanSpace ℝ (Fin k))
    (hEcont : ∀ j, ContinuousOn (E j) (F j))
    (hEinj : ∀ j, Set.InjOn (E j)
      (F j ∩ bohrHullKernel f (Submodule.span ℚ (Γa : Set ℝ)))) : r ≤ k :=
  card_le_of_hull_charts_rel hf htb (Submodule.span ℚ (Γa : Set ℝ))
    (HTGeometry.linearIndependent_mkQ_of_int hind) hlam F hFclosed hcover E hEcont hEinj

/-- **The relative frequency-rank law.**  The rational rank of the frequency group of the carrier,
relative to a subgroup of it, is at most the dimension of a chart atlas injective on the fibre over
that subgroup — with no bound at all on the subgroup itself. -/
theorem rank_quotient_bohrHullFrequencies_le_of_charts_rel
    (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (Γa : AddSubgroup ℝ)
    {N k : ℕ} (F : Fin N → Set (BohrHull f)) (hFclosed : ∀ j, IsClosed (F j))
    (hcover : ∀ x : BohrHull f, ∃ j, x ∈ F j)
    (E : Fin N → BohrHull f → EuclideanSpace ℝ (Fin k))
    (hEcont : ∀ j, ContinuousOn (E j) (F j))
    (hEinj : ∀ j, Set.InjOn (E j)
      (F j ∩ bohrHullKernel f (Submodule.span ℚ (Γa : Set ℝ)))) :
    Module.rank ℤ ((bohrHullFrequencies f) ⧸ (Γa.addSubgroupOf (bohrHullFrequencies f)))
      ≤ (k : Cardinal) := by
  classical
  set H : AddSubgroup ℝ := bohrHullFrequencies f with hH
  set Q := (H ⧸ (Γa.addSubgroupOf H)) with hQ
  refine rank_le fun s hs => ?_
  set e : Fin (Fintype.card ↥s) ≃ ↥s := (Fintype.equivFin ↥s).symm with hedef
  -- representatives of the classes
  set y : ↥s → ↥H := fun i => Quotient.out ((i : Q)) with hy
  set lam : Fin (Fintype.card ↥s) → ℝ := fun j => ((y (e j) : ↥H) : ℝ) with hlamdef
  have hmk : ∀ i : ↥s, (QuotientAddGroup.mk (y i) : Q) = (i : Q) := by
    intro i
    exact Quotient.out_eq _
  have hlamfreq : ∀ j, IsBohrHullFrequency f (lam j) := by
    intro j
    exact mem_bohrHullFrequencies.mp (y (e j)).2
  have hind : ∀ c : Fin (Fintype.card ↥s) → ℤ,
      (∑ j, (c j : ℝ) * lam j) ∈ Γa → ∀ j, c j = 0 := by
    intro c hc j
    -- the integral combination of the representatives lies in the subgroup
    have hmem : (∑ j, c j • (y (e j))) ∈ Γa.addSubgroupOf H := by
      have hval : (((∑ j, c j • (y (e j))) : ↥H) : ℝ) = ∑ j, (c j : ℝ) * lam j := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hlamdef, zsmul_eq_mul]
      rw [AddSubgroup.mem_addSubgroupOf]
      rw [hval]
      exact hc
    have hzeroQ : (∑ j, c j • ((e j : ↥s) : Q)) = 0 := by
      set π : ↥H →+ Q := QuotientAddGroup.mk' (Γa.addSubgroupOf H) with hπ
      have hstep : ∀ i : ↥s, π (y i) = (i : Q) := fun i => hmk i
      have hrw : (∑ j, c j • ((e j : ↥s) : Q)) = π (∑ j, c j • (y (e j))) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_zsmul, hstep]
      rw [hrw]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hmem
    have hindep := (Fintype.linearIndependent_iff.mp (hs.comp e e.injective))
    exact hindep c hzeroQ j
  have hcard := card_le_of_int_independent_mod hf htb Γa hlamfreq hind F hFclosed hcover E
    hEcont hEinj
  rwa [Fintype.card_coe] at hcard

end GaloisForLFunctions
