import GaloisForLFunctions.HTGeometry.BohrHullCharRealization
import GaloisForLFunctions.HTGeometry.BohrHullSeparation

/-!
# The `r`-parameter subgroup of the phase carrier

A rationally independent packet of frequencies spans a `ℚ`-subspace of `ℝ` on which the assignment
`λ_j ↦ e_j` is `ℚ`-linear; extending it to all of `ℝ` gives a `ℚ`-linear map `v : ℝ → ℝ^r`, and
`γ ↦ e^{i ⟨v γ, t⟩}` is then a unimodular character of the frequency group for every parameter `t`.
Realising those characters inside the hull produces a map `ℝ^r → hull` whose `j`-th frequency
character is `t ↦ e^{i t_j}`.

The map is continuous for a structural reason: frequency characters separate the points of the
compact hull, so the evaluation map into the product of circles is a homeomorphism onto its image,
and the composite parameter family is visibly continuous there.  No continuous section of the
carrier over the torus is needed — and none exists when the carrier is solenoidal.
-/

open Finset

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {f : ℝ →ᵇ ℂ}

/-- A rationally independent finite family of reals admits a `ℚ`-linear functional package sending
it to the standard basis of `ℝ^r`. -/
theorem exists_rat_linear_dual {r : ℕ} {lam : Fin r → ℝ} (hind : LinearIndependent ℚ lam) :
    ∃ v : ℝ →ₗ[ℚ] (Fin r → ℝ), ∀ j, v (lam j) = Pi.single j (1 : ℝ) := by
  classical
  set B : Module.Basis (Fin r) ℚ (Submodule.span ℚ (Set.range lam)) := Module.Basis.span hind with hB
  set v0 : (Submodule.span ℚ (Set.range lam)) →ₗ[ℚ] (Fin r → ℝ) :=
    B.constr ℚ (fun j => Pi.single j (1 : ℝ)) with hv0
  obtain ⟨v, hv⟩ := v0.exists_extend
  refine ⟨v, fun j => ?_⟩
  have hmem : lam j ∈ Submodule.span ℚ (Set.range lam) :=
    Submodule.subset_span ⟨j, rfl⟩
  have hBj : ((B j : Submodule.span ℚ (Set.range lam)) : ℝ) = lam j := by
    rw [hB, Module.Basis.span_apply hind j]
  have happ : v ((B j : Submodule.span ℚ (Set.range lam)) : ℝ) = v0 (B j) := by
    have := congrArg (fun L : (Submodule.span ℚ (Set.range lam)) →ₗ[ℚ] (Fin r → ℝ) => L (B j)) hv
    simpa using this
  rw [← hBj, happ, hv0]
  simp

/-- **The phase carrier carries an `r`-parameter subgroup adapted to an independent packet.** -/
theorem exists_continuous_hullParameter (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {r : ℕ} {lam : Fin r → ℝ} (hind : LinearIndependent ℚ lam)
    (hlam : ∀ j, IsBohrHullFrequency f (lam j)) :
    ∃ φ : (Fin r → ℝ) → BohrHull f, Continuous φ ∧
      ∀ (t : Fin r → ℝ) (j : Fin r),
        bohrHullChar f (lam j) (φ t) = Complex.exp ((t j : ℂ) * Complex.I) := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  obtain ⟨v, hv⟩ := exists_rat_linear_dual hind
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
  have hval : ∀ (t : Fin r → ℝ) (j : Fin r),
      bohrHullChar f (lam j) (φ t) = Complex.exp ((t j : ℂ) * Complex.I) := by
    intro t j
    have hsum : (∑ i, v (lam j) i * t i) = t j := by
      rw [hv j]
      have hterm : ∀ i : Fin r, (Pi.single j (1 : ℝ) : Fin r → ℝ) i * t i
          = if i = j then t i else 0 := by
        intro i
        by_cases h : i = j <;> simp [h]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ j t]
      simp
    rw [hφ t (lam j) (hlam j), hωdef]
    simp only [hsum]
  refine ⟨φ, ?_, hval⟩
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
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij) (hEcont.subtype_mk _) with hedef
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

end GaloisForLFunctions
