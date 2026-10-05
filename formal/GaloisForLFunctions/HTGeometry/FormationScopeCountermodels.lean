import GaloisForLFunctions.HTGeometry.PositiveTwoSidedDustSelection

/-!
# Countermodels for the formation compactification

The total mass `Φ ↦ Φ(1)` is a continuous character of `M(K)`, since `(Φ ⋆ Ψ)(1) = Φ(1) Ψ(1)`.

1. **Finite packets are not closed.**  `(δ_1 + z δ_1/N)^N → Exp_⋆(z δ_1)`, and `Exp_⋆(z δ_1)` is not
   a finite formation: its mass `e^z` has no zero, while a finite formation has mass
   `Π_j (1 + z α_j(K))`, which vanishes somewhere unless it is constant.
2. **Zeros do not see dust.**  Every continuous character sends `Exp_⋆(zγ)` to the zero-free
   `exp(z χ(γ))`; the zeros of `χ(F(z))` do not depend on the dust.
3. **Higher collisions do not see dust** (`cumulant_dust_invariant`).
4. **The first response does not separate dust from atoms.**  `Exp_⋆(z δ_1)` and `δ_1 + z δ_1` have
   the same first cumulant `δ_1` but different formations (`C_2 = 0` versus `-δ_1/2`).
5. **Positivity is load-bearing.**  The signed packets `(N δ_1, -N δ_1)` have first response `0`,
   but their formations have mass `1 - N² z²`, so no subsequence converges.
6. **Uniform mass is load-bearing.**  The positive packets `(N δ_1)` have formation mass `1 + N z`,
   and no subsequence converges.
9. **A noninvertible observer erases data.**  Pushforward along the constant endomorphism
   `x ↦ 1` sends every `Φ` to `Φ(1) δ_1`; distinct points give distinct Dirac masses with equal
   images.
-/

open Filter Topology NormedSpace MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [CommMonoid K] [ContinuousMul K] [MeasurableSpace K] [BorelSpace K]

open MeasureAlgebra

attribute [local instance] ratAlgebra

/-! ### The mass character -/

omit [T2Space K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem rightTransform_one_fun (Ψ : MeasureAlgebra K) :
    rightTransform Ψ (1 : C(K, ℂ)) = Ψ 1 • (1 : C(K, ℂ)) := by
  ext x
  rw [rightTransform_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
    mul_one]
  congr 1

/-- The total mass `Φ ↦ Φ(1)`, a character of `M(K)`. -/
def massHom : MeasureAlgebra K →+* ℂ where
  toFun Φ := Φ 1
  map_one' := by simp
  map_mul' Φ Ψ := by rw [mul_apply, rightTransform_one_fun, map_smul, smul_eq_mul, mul_comm]
  map_zero' := rfl
  map_add' _ _ := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem massHom_apply (Φ : MeasureAlgebra K) : massHom Φ = Φ 1 := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem continuous_massHom : Continuous (massHom (K := K)) :=
  (evalAt (1 : C(K, ℂ))).continuous

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem massHom_smul (c : ℂ) (Φ : MeasureAlgebra K) : massHom (c • Φ) = c * massHom Φ := rfl

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Continuous characters commute with the convolution exponential. -/
theorem character_exp (χ : MeasureAlgebra K →+* ℂ) (hχ : Continuous χ) (X : MeasureAlgebra K) :
    χ (exp X) = Complex.exp (χ X) := by
  rw [map_exp χ hχ, Complex.exp_eq_exp_ℂ]

/-! ### 1. Finite packets are not closed -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem massHom_formation {m : ℕ} (A : Fin m → MeasureAlgebra K) (z : ℂ) :
    massHom (formation A z) = ∏ j, (1 + z * massHom (A j)) := by
  simp [formation, map_prod, massHom_smul]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- `Exp_⋆(z δ_1)` is not the formation of any finite packet. -/
theorem formation_ne_exp {m : ℕ} (A : Fin m → MeasureAlgebra K) :
    formation A ≠ fun z => exp (z • (1 : MeasureAlgebra K)) := by
  intro h
  have hz : ∀ z : ℂ, ∏ j, (1 + z * massHom (A j)) = Complex.exp z := fun z => by
    have := congrArg massHom (congrFun h z)
    rwa [massHom_formation, character_exp _ continuous_massHom, massHom_smul, map_one,
      mul_one] at this
  have hc : ∀ j, massHom (A j) = 0 := by
    intro j
    by_contra hj
    have := hz (-(massHom (A j))⁻¹)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by field_simp; ring)] at this
    exact Complex.exp_ne_zero _ this.symm
  have h1 := hz 1
  simp only [hc, mul_zero, add_zero, Finset.prod_const_one] at h1
  have h2 : Real.exp 1 = 1 := by exact_mod_cast (Complex.ofReal_exp 1).trans h1.symm
  exact absurd h2 (ne_of_gt (Real.one_lt_exp_iff.2 one_pos))

/-- **Countermodel 1.**  For `C ≥ 1` the finite positive formations of mass `≤ C` are not closed
in the compact-open weak topology: `Exp_⋆(z δ_1)` is a limit of them but not one of them. -/
theorem not_isClosed_packetFormationSet {C : ℝ} (hC : 1 ≤ C) :
    ¬ IsClosed (inFormSpace (packetFormationSet (K := K) C)) := by
  intro hclosed
  have hmem : (fun z => exp (z • (1 : MeasureAlgebra K))) ∈
      inFormSpace (decoratedSet (K := K) C) := by
    refine ⟨1, 0, isPositive_one, fun _ => isPositive_zero, by simp, by simpa using hC, ?_⟩
    funext z
    simp [decorated]
  rw [← closure_packetFormationSet, hclosed.closure_eq] at hmem
  obtain ⟨m, A, -, -, hA⟩ := hmem
  exact formation_ne_exp A hA.symm

/-! ### 2. Zeros do not see dust -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Countermodel 2.**  A continuous character never vanishes on the dust factor, so the zeros
of `χ(F(z))` are those of the atomic product, whatever the dust. -/
theorem character_decorated_eq_zero_iff (χ : MeasureAlgebra K →+* ℂ) (hχ : Continuous χ)
    (γ γ' : MeasureAlgebra K) (α : ℕ → MeasureAlgebra K) (z : ℂ) :
    χ (decorated γ α z) = 0 ↔ χ (decorated γ' α z) = 0 := by
  simp only [decorated, map_mul, character_exp χ hχ, mul_eq_zero, Complex.exp_ne_zero, false_or]

/-! ### 4. The first response does not separate dust from atoms -/

/-- The single-atom packet `(δ_1, 0, 0, …)`. -/
def unitAtom : ℕ → MeasureAlgebra K := fun j => if j = 0 then 1 else 0

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem summable_unitAtom : Summable fun j => ‖unitAtom (K := K) j‖ :=
  summable_of_ne_finset_zero (s := {0}) fun j hj => by
    simp [unitAtom, Finset.mem_singleton.not.1 hj]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem tsum_unitAtom : ∑' j, unitAtom (K := K) j = 1 := by
  rw [tsum_eq_single 0 fun j hj => by simp [unitAtom, hj]]
  simp [unitAtom]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Countermodel 4.**  Pure dust `Exp_⋆(z δ_1)` and the single atom `δ_1 + z δ_1` have the same
first cumulant but are different formations. -/
theorem firstCumulant_does_not_separate :
    cumulant (1 : MeasureAlgebra K) 0 1 = cumulant 0 unitAtom 1 ∧
      decorated (1 : MeasureAlgebra K) 0 ≠ decorated 0 unitAtom := by
  refine ⟨by rw [cumulant_one, cumulant_one, tsum_unitAtom]; simp, fun h => ?_⟩
  have hc := congrFun (cumulant_eq_of_decorated_eq (by simp) summable_unitAtom one_pos
    fun z _ => congrFun h z) 2
  rw [cumulant_of_two_le _ _ le_rfl, cumulant_of_two_le _ _ le_rfl] at hc
  have h2 : ∑' j, unitAtom (K := K) j ^ 2 = 1 := by
    rw [tsum_eq_single 0 fun j hj => by simp [unitAtom, hj]]
    simp [unitAtom]
  rw [h2] at hc
  have h3 := congrArg massHom hc
  simp [massHom_smul, logCoeff] at h3
  norm_num at h3

/-! ### 5–6. Positivity and uniform mass are load-bearing -/

omit [CompactSpace K] [T2Space K] [SecondCountableTopology K] [CommMonoid K] [ContinuousMul K]
  [MeasurableSpace K] [BorelSpace K] in
/-- No subsequence converges when the masses at `z = 1` are unbounded along it. -/
theorem not_formConv_of_unbounded {F : ℕ → ℂ → MeasureAlgebra K} {G : ℂ → MeasureAlgebra K}
    (hF : ∀ M : ℝ, ∃ N, ∀ n, N ≤ n → M < ‖F n 1 1‖) : ¬ FormConv F G := by
  intro h
  have ht := (h 1 1).tendsto_at (x := 1) (mem_closedBall_zero_iff.2 (by norm_num))
  obtain ⟨M, hM⟩ := ht.norm.bddAbove_range
  obtain ⟨N, hN⟩ := hF M
  exact absurd (hM ⟨N, rfl⟩) (not_le.2 (hN N le_rfl))

/-- The signed packet `(N δ_1, -N δ_1)`. -/
def signedPacket (N : ℕ) : Fin 2 → MeasureAlgebra K := ![(N : ℂ) • 1, -((N : ℂ) • 1)]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Countermodel 5.**  The signed packets have vanishing first response, yet no subsequence of
their formations converges. -/
theorem signedPacket_counterexample :
    (∀ N, ∑ j, signedPacket (K := K) N j = 0) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ G : ℂ → MeasureAlgebra K,
        ¬ FormConv (fun n => formation (signedPacket (φ n))) G := by
  refine ⟨fun N => by simp [signedPacket], fun φ hφ G => not_formConv_of_unbounded fun M => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (M + 2)
  refine ⟨N, fun n hn => ?_⟩
  have hmass : formation (signedPacket (K := K) (φ n)) 1 1 = 1 - ((φ n : ℂ)) ^ 2 := by
    have := massHom_formation (signedPacket (K := K) (φ n)) 1
    simp only [massHom_apply] at this
    rw [this]
    simp [signedPacket, Fin.prod_univ_two]
    ring
  rw [hmass]
  have hφn : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  have hN' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (φ n : ℝ) ^ 2 - 1 ≤ ‖(1 : ℂ) - (φ n : ℂ) ^ 2‖ := by
    rw [show (1 : ℂ) - (φ n : ℂ) ^ 2 = ((1 - (φ n : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    have := neg_le_abs (1 - (φ n : ℝ) ^ 2)
    linarith
  nlinarith [sq_nonneg ((φ n : ℝ) - 1)]

/-- The positive one-atom packet `(N δ_1)`. -/
def massPacket (N : ℕ) : Fin 1 → MeasureAlgebra K := ![(N : ℂ) • 1]

omit [SecondCountableTopology K] in
/-- **Countermodel 6.**  The positive packets `(N δ_1)` have unbounded mass, and no subsequence of
their formations converges. -/
theorem massPacket_counterexample :
    (∀ N j, IsPositive (massPacket (K := K) N j)) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ G : ℂ → MeasureAlgebra K,
        ¬ FormConv (fun n => formation (massPacket (φ n))) G := by
  refine ⟨fun N j => ?_, fun φ hφ G => not_formConv_of_unbounded fun M => ?_⟩
  · fin_cases j
    have h := IsPositive.smul (isPositive_one (K := K)) (Nat.cast_nonneg (α := ℝ) N)
    simpa [massPacket] using h
  obtain ⟨N, hN⟩ := exists_nat_gt M
  refine ⟨N, fun n hn => ?_⟩
  have hmass : formation (massPacket (K := K) (φ n)) 1 1 = 1 + (φ n : ℂ) := by
    have := massHom_formation (massPacket (K := K) (φ n)) 1
    simp only [massHom_apply] at this
    rw [this]
    simp [massPacket]
  rw [hmass, show (1 : ℂ) + (φ n : ℂ) = ((1 + (φ n : ℝ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hφn : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  have hN' : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-! ### 9. A noninvertible observer erases data -/

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Pushforward along the constant endomorphism `x ↦ 1` keeps only the total mass. -/
theorem push_one (Φ : MeasureAlgebra K) :
    pushAlgHom (1 : K →ₜ* K) Φ = Φ 1 • (1 : MeasureAlgebra K) := by
  ext f
  rw [pushAlgHom_apply, push_apply, MeasureAlgebra.smul_apply, one_apply]
  have : f.comp (1 : K →ₜ* K).toContinuousMap = f 1 • (1 : C(K, ℂ)) := by
    ext x
    simp
  rw [this, map_smul, smul_eq_mul, mul_comm]

omit [SecondCountableTopology K] in
/-- **Countermodel 9.**  Distinct points give distinct Dirac masses whose images under the
constant observer coincide. -/
theorem constant_observer_erases {x y : K} (hxy : x ≠ y) :
    ofMeasure (diracMeasure x) ≠ ofMeasure (diracMeasure y) ∧
      pushAlgHom (1 : K →ₜ* K) (ofMeasure (diracMeasure x)) =
        pushAlgHom (1 : K →ₜ* K) (ofMeasure (diracMeasure y)) := by
  refine ⟨fun h => ?_, by rw [push_one, push_one]; simp [ofMeasure_diracMeasure]⟩
  obtain ⟨a, ha⟩ := exists_continuousMap_ne hxy
  have := congrArg (fun Φ : MeasureAlgebra K => Φ a) h
  simp only [ofMeasure_diracMeasure] at this
  exact ha this

end GaloisForLFunctions.HTGeometry.FormationDust
