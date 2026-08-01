import GaloisForLFunctions.HTGeometry.BohrHullParameterSubgroup
import GaloisForLFunctions.HTGeometry.CubeFaceDimensionBound

/-!
# The frequency rank is bounded by the dimension of a carrier embedding

An almost periodic function whose phase carrier embeds continuously and injectively into a
finite-dimensional space cannot have more rationally independent Bohr frequencies than that
dimension.

The `r`-parameter subgroup of the carrier turns the cube `[0,1]^r` into a map whose `j`-th pair of
opposite faces lands in `{χ_j = 1}` and `{χ_j = −1}` — two disjoint compact sets, since the
embedding is injective and the parameter subgroup realises both phases.  The cube-face dimension
bound then reads off `r ≤ dim`.  This is the dimension step of the finite-phase law, and with it the
finite rational rank of the frequency group follows from any finite-dimensional embedding of the
carrier, such as a jet embedding coming from an algebraic differential equation.
-/

open Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {f : ℝ →ᵇ ℂ}

/-- **The rational frequency rank is bounded by the dimension of any carrier embedding.** -/
theorem rank_le_finrank_of_hull_embedding (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {r : ℕ} {lam : Fin r → ℝ} (hind : LinearIndependent ℚ lam)
    (hlam : ∀ j, IsBohrHullFrequency f (lam j))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Φ : BohrHull f → E} (hΦ : Continuous Φ) (hΦinj : Function.Injective Φ) :
    r ≤ Module.finrank ℝ E := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  obtain ⟨φ, hφcont, hφval⟩ := exists_continuous_hullParameter hf htb hind hlam
  -- the two closed sets attached to each frequency
  set A : Fin r → Set E := fun j => Φ '' {x : BohrHull f | bohrHullChar f (lam j) x = 1} with hAdef
  set B : Fin r → Set E := fun j => Φ '' {x : BohrHull f | bohrHullChar f (lam j) x = -1} with hBdef
  have hAcl : ∀ j, IsCompact (A j) := by
    intro j
    refine IsCompact.image ?_ hΦ
    exact (isClosed_singleton.preimage (continuous_bohrHullChar f (lam j))).isCompact
  have hBcl : ∀ j, IsCompact (B j) := by
    intro j
    refine IsCompact.image ?_ hΦ
    exact (isClosed_singleton.preimage (continuous_bohrHullChar f (lam j))).isCompact
  have hAne : ∀ j, (A j).Nonempty := by
    intro j
    refine ⟨Φ (φ (fun _ => 0)), ?_⟩
    refine ⟨φ (fun _ => 0), ?_, rfl⟩
    have := hφval (fun _ => (0:ℝ)) j
    simpa using this
  have hBne : ∀ j, (B j).Nonempty := by
    intro j
    refine ⟨Φ (φ (fun i => if i = j then Real.pi else 0)), ?_⟩
    refine ⟨φ (fun i => if i = j then Real.pi else 0), ?_, rfl⟩
    have hv := hφval (fun i => if i = j then Real.pi else 0) j
    rw [Set.mem_setOf_eq, hv, if_pos rfl]
    exact Complex.exp_pi_mul_I
  have hdisj : ∀ j, Disjoint (A j) (B j) := by
    intro j
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
    have hxe : x' = x := hΦinj hxx'
    rw [hxe] at hx'
    rw [Set.mem_setOf_eq] at hx hx'
    rw [hx] at hx'
    norm_num at hx'
  -- the cube map
  set γ : EuclideanSpace ℝ (Fin r) → E :=
    fun x => Φ (φ (fun j => Real.pi * x j)) with hγdef
  have hγcont : Continuous γ := by
    refine hΦ.comp (hφcont.comp ?_)
    exact continuous_pi fun j => continuous_const.mul (PiLp.continuous_apply 2 _ j)
  refine le_finrank_of_cube_faces hAcl hAne hBcl hBne hdisj (γ := γ) hγcont.continuousOn
    (S := Set.range Φ) (fun x _ => ⟨_, rfl⟩) ?_ ?_
  · intro x _ j hxj
    refine ⟨φ (fun i => Real.pi * x i), ?_, rfl⟩
    have hv := hφval (fun i => Real.pi * x i) j
    rw [Set.mem_setOf_eq, hv, hxj]
    simp
  · intro x _ j hxj
    refine ⟨φ (fun i => Real.pi * x i), ?_, rfl⟩
    have hv := hφval (fun i => Real.pi * x i) j
    rw [Set.mem_setOf_eq, hv, hxj, mul_one]
    exact Complex.exp_pi_mul_I

/-- **No more rationally independent frequencies than the dimension of a carrier embedding.** -/
theorem card_le_finrank_of_hull_embedding (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {s : Finset ℝ} (hsfreq : ∀ γ ∈ s, IsBohrHullFrequency f γ)
    (hind : LinearIndependent ℚ (fun γ : s => (γ : ℝ)))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Φ : BohrHull f → E} (hΦ : Continuous Φ) (hΦinj : Function.Injective Φ) :
    s.card ≤ Module.finrank ℝ E := by
  classical
  set e : Fin s.card ≃ s :=
    (finCongr (Fintype.card_coe s)).symm.trans (Fintype.equivFin (s : Finset ℝ)).symm with hedef
  set lam : Fin s.card → ℝ := fun i => ((e i : s) : ℝ) with hlamdef
  have hindlam : LinearIndependent ℚ lam := hind.comp e e.injective
  have hfreqlam : ∀ i, IsBohrHullFrequency f (lam i) := fun i => hsfreq _ (e i).2
  exact rank_le_finrank_of_hull_embedding hf htb hindlam hfreqlam hΦ hΦinj

/-- Family form of the frequency-rank bound. -/
theorem card_le_finrank_of_hull_embedding_family (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hind : LinearIndependent ℚ lam)
    (hfreq : ∀ i, IsBohrHullFrequency f (lam i))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Φ : BohrHull f → E} (hΦ : Continuous Φ) (hΦinj : Function.Injective Φ) :
    Fintype.card ι ≤ Module.finrank ℝ E := by
  classical
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hedef
  have hind' : LinearIndependent ℚ (lam ∘ e) := hind.comp e e.injective
  exact rank_le_finrank_of_hull_embedding hf htb hind' (fun i => hfreq (e i)) hΦ hΦinj

/-- **Finite rational rank of the frequency group.** -/
theorem rank_bohrHullFrequencies_le (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Φ : BohrHull f → E} (hΦ : Continuous Φ) (hΦinj : Function.Injective Φ) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ (Module.finrank ℝ E : Cardinal) := by
  classical
  refine rank_le fun s hs => ?_
  set lam : (↥s) → ℝ := fun i => ((i : bohrHullFrequencies f) : ℝ) with hlamdef
  have hker : LinearMap.ker ((bohrHullFrequencies f).subtype.toIntLinearMap) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact Subtype.ext hxy
  have hZ : LinearIndependent ℤ lam := by
    have h := hs.map' ((bohrHullFrequencies f).subtype.toIntLinearMap) hker
    exact h
  have hQ : LinearIndependent ℚ lam := (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mp hZ
  have hfreq : ∀ i : ↥s, IsBohrHullFrequency f (lam i) :=
    fun i => mem_bohrHullFrequencies.mp (i : bohrHullFrequencies f).2
  have hcard := card_le_finrank_of_hull_embedding_family hf htb hQ hfreq hΦ hΦinj
  rwa [Fintype.card_coe] at hcard

end GaloisForLFunctions
