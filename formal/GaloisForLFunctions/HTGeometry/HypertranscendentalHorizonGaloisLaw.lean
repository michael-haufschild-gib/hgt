import GaloisForLFunctions.HTGeometry.CriticalHorizonConstantDescent
import GaloisForLFunctions.HTGeometry.HypertranscendentalHorizonFunctionField
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFiniteJetRank
import GaloisForLFunctions.HTGeometry.SheetActionRadicals
import GaloisForLFunctions.HTGeometry.CriticalHorizonRadicalRegime
import GaloisForLFunctions.HTGeometry.AlgebraicMatroidFieldRank

/-!
# Maximal finite-horizon Galois ambiguity of a hypertranscendental source

Let `f` be hypertranscendental over a characteristic-zero field `F`, with divided jets
`x_i = D^i f / i!` and reciprocal divided jets `y_j = D^j(f⁻¹)/j!`, so that
`(∑ x_i t^i)(∑ y_j t^j) = 1` as formal Taylor series.  Put `L = m + n`,

`K_L = F(x_0,…,x_{L-1})`, `H_{m,n} = F(x_m,…,x_{L-1}, y_n,…,y_{L-1})`.

The divided jets of a hypertranscendental element are algebraically independent, so evaluation at
them identifies the generic critical source and observation fields with `K_L ⊇ H_{m,n}`: the
generic reciprocal coordinates go to the `y_j` because both sides satisfy the same inverse
recursion.  Transporting the critical horizon over `F`:

* `[K_L : H_{m,n}] = choose(m+n, m)`;
* the Galois group of the normal closure acts on the sheets as the full symmetric group;
* no field lies strictly between `H_{m,n}` and `K_L`;
* `K_L/H_{m,n}` is solvable by radicals exactly for `(m,n) ∈ {(1,1),(1,2),(2,1),(1,3),(3,1)}`;
* the finite horizon field `O_{a,b;N} = F(x_a,…,x_N, y_b,…,y_N)` has transcendence degree
  `min(N+1, (N+1-a) + (N+1-b))`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- Scaling each member of an algebraically independent family by a nonzero constant keeps it
algebraically independent. -/
theorem algebraicIndependent_smul_of_ne_zero {F A ι : Type*} [Field F] [CommRing A] [Algebra F A]
    {v : ι → A} (hv : AlgebraicIndependent F v) (c : ι → F) (hc : ∀ i, c i ≠ 0) :
    AlgebraicIndependent F (fun i => c i • v i) := by
  rw [algebraicIndependent_iff_injective_aeval] at hv ⊢
  let φ : MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
    MvPolynomial.aeval fun i => MvPolynomial.C (c i) * MvPolynomial.X i
  let ψ : MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
    MvPolynomial.aeval fun i => MvPolynomial.C (c i)⁻¹ * MvPolynomial.X i
  have hψφ : ψ.comp φ = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, φ, ψ, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply, ← mul_assoc, ← MvPolynomial.C_mul,
      mul_inv_cancel₀ (hc i), MvPolynomial.C_1, one_mul]
  have hφ : Function.Injective φ := by
    intro p q h
    have := congrArg ψ h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hψφ] at this
  have hcomp : MvPolynomial.aeval (fun i => c i • v i) = (MvPolynomial.aeval v).comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [φ, Algebra.smul_def]
  rw [hcomp]
  exact hv.comp hφ

variable {E : Type*} [Field E] [Differential E]

/-- The divided jet `D^i x / i!`. -/
def dividedJet (x : E) (i : ℕ) : E :=
  differentialJet i x / (i.factorial : E)

/-- The iterated derivatives of `1` vanish above order zero. -/
theorem differentialJet_one_succ (k : ℕ) : differentialJet (k + 1) (1 : E) = 0 := by
  induction k with
  | zero =>
      rw [differentialJet_succ, differentialJet_zero]
      exact Derivation.map_one_eq_zero _
  | succ k ih =>
      rw [differentialJet_succ, ih]
      exact map_zero _

/-- **The divided jets of `x` and `x⁻¹` are inverse Taylor coefficients.** -/
theorem sum_dividedJet_mul_dividedJet_inv [CharZero E] {x : E} (hx : x ≠ 0) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), dividedJet x i * dividedJet x⁻¹ (k - i) =
      if k = 0 then 1 else 0 := by
  have hleib := differentialJet_mul_binomial' k x x⁻¹
  rw [mul_inv_cancel₀ hx] at hleib
  have hk : (k.factorial : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hsum : ∑ i ∈ Finset.range (k + 1), dividedJet x i * dividedJet x⁻¹ (k - i) =
      differentialJet k (1 : E) / (k.factorial : E) := by
    rw [hleib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi0 : (i.factorial : E) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hki0 : ((k - i).factorial : E) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - i))
    have hchoose : (k.choose i : E) * i.factorial * (k - i).factorial = k.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
    rw [dividedJet, dividedJet, nsmul_eq_mul]
    field_simp
    rw [← hchoose]
    ring
  rw [hsum]
  rcases k with _ | k
  · simp
  · rw [differentialJet_one_succ, zero_div]
    simp

/-- The truncated divided-jet polynomial `∑_{i ≤ N} x_i t^i`. -/
def dividedJetPolynomial (x : E) (N : ℕ) : E[X] :=
  ∑ i ∈ Finset.range (N + 1), C (dividedJet x i) * X ^ i

theorem coeff_dividedJetPolynomial (x : E) (N k : ℕ) :
    (dividedJetPolynomial x N).coeff k = if k ≤ N then dividedJet x k else 0 := by
  rw [dividedJetPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem coeff_dividedJetPolynomial_of_le (x : E) {N k : ℕ} (hk : k ≤ N) :
    (dividedJetPolynomial x N).coeff k = dividedJet x k := by
  rw [coeff_dividedJetPolynomial, if_pos hk]

/-- **The truncated divided-jet polynomials of `x` and `x⁻¹` are inverse modulo `t^{N+1}`.** -/
theorem X_pow_dvd_dividedJetPolynomial_mul_sub_one [CharZero E] {x : E} (hx : x ≠ 0) (N : ℕ) :
    (X : E[X]) ^ (N + 1) ∣ dividedJetPolynomial x N * dividedJetPolynomial x⁻¹ N - 1 := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (dividedJetPolynomial x N).coeff i * (dividedJetPolynomial x⁻¹ N).coeff j)]
  have hterm : ∑ k ∈ Finset.range d.succ,
      (dividedJetPolynomial x N).coeff k * (dividedJetPolynomial x⁻¹ N).coeff (d - k) =
        ∑ k ∈ Finset.range (d + 1), dividedJet x k * dividedJet x⁻¹ (d - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coeff_dividedJetPolynomial_of_le x (by omega),
      coeff_dividedJetPolynomial_of_le x⁻¹ (by omega)]
  rw [hterm, sum_dividedJet_mul_dividedJet_inv hx d, Polynomial.coeff_one]
  split_ifs <;> simp_all

section GenericPoint

variable {F : Type*} [Field F] [Algebra F E] {f : E}

/-- A hypertranscendental element is nonzero. -/
theorem hypertranscendentalOver_ne_zero (hf : HypertranscendentalOver F f) : f ≠ 0 := by
  intro h0
  have hind := finiteDifferentialJet_algebraicIndependent_of_hypertranscendentalOver hf 1
  have := hind.ne_zero (0 : Fin 1)
  apply this
  simp [finiteDifferentialJet, h0]

/-- **The divided jets of a hypertranscendental element are algebraically independent.** -/
theorem dividedJet_algebraicIndependent [CharZero F] (hf : HypertranscendentalOver F f) (L : ℕ) :
    AlgebraicIndependent F (fun i : Fin L => dividedJet f i) := by
  have h := algebraicIndependent_smul_of_ne_zero
    (finiteDifferentialJet_algebraicIndependent_of_hypertranscendentalOver hf L)
    (fun i : Fin L => (((i : ℕ).factorial : F))⁻¹)
    (fun i => inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
  convert h using 1
  funext i
  rw [dividedJet, finiteDifferentialJet, Algebra.smul_def, map_inv₀, map_natCast,
    div_eq_inv_mul]

variable (hf : HypertranscendentalOver F f) (N : ℕ)
include hf

theorem isUnit_coeff_zero_dividedJetPolynomial :
    IsUnit ((dividedJetPolynomial f N).coeff 0) := by
  rw [coeff_dividedJetPolynomial_of_le f (Nat.zero_le N), dividedJet]
  simp [isUnit_iff_ne_zero, hypertranscendentalOver_ne_zero hf]

/-- Evaluation of the generic jet algebra at the divided jets of `f`. -/
def hypertranscendentalJetLift : genericJetAlgebra F N →ₐ[F] E :=
  jetLiftₐ (fun i : Fin (N + 1) => (dividedJetPolynomial f N).coeff i)
    (by simpa using isUnit_coeff_zero_dividedJetPolynomial hf N)

theorem hypertranscendentalJetLift_algebraMap (p : genericJetRing F N) :
    hypertranscendentalJetLift hf N (algebraMap (genericJetRing F N) (genericJetAlgebra F N) p) =
      MvPolynomial.aeval (fun i : Fin (N + 1) => (dividedJetPolynomial f N).coeff i) p := by
  rw [hypertranscendentalJetLift, jetLiftₐ_apply, jetLift_algebraMap]

theorem hypertranscendentalJetLift_raw {j : ℕ} (hj : j < N + 1) :
    hypertranscendentalJetLift hf N (genericRaw F N j) = dividedJet f j := by
  rw [hypertranscendentalJetLift, jetLiftₐ_apply, jetLift_genericRaw _ _ hj]
  exact coeff_dividedJetPolynomial_of_le f (Nat.lt_succ_iff.mp hj)

theorem hypertranscendentalJetLift_recip [CharZero F] {j : ℕ} (hj : j ≤ N) :
    hypertranscendentalJetLift hf N (genericRecip F N j) = dividedJet f⁻¹ j := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  rw [hypertranscendentalJetLift, jetLiftₐ_apply,
    jetLift_genericRecip (X_pow_dvd_dividedJetPolynomial_mul_sub_one
      (hypertranscendentalOver_ne_zero hf) N)
    (isUnit_coeff_zero_dividedJetPolynomial hf N) j hj]
  exact coeff_dividedJetPolynomial_of_le f⁻¹ hj

theorem hypertranscendentalJetLift_injective [CharZero F] :
    Function.Injective (hypertranscendentalJetLift hf N) := by
  have hind : AlgebraicIndependent F
      (fun i : Fin (N + 1) => (dividedJetPolynomial f N).coeff (i : ℕ)) := by
    convert dividedJet_algebraicIndependent hf (N + 1) using 1
    funext i
    exact coeff_dividedJetPolynomial_of_le f (Nat.lt_succ_iff.mp i.isLt)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (MvPolynomial.X (0 : Fin (N + 1)) : genericJetRing F N)) z
  have hspec := IsLocalization.mk'_spec (genericJetAlgebra F N) p s
  have hmap := congrArg (hypertranscendentalJetLift hf N) hspec
  rw [map_mul, hz, zero_mul, hypertranscendentalJetLift_algebraMap] at hmap
  have hp : p = 0 := (algebraicIndependent_iff_injective_aeval.mp hind)
    (by rw [← hmap, map_zero])
  simp [hp]

/-- The generic point of the finite jet field: evaluation at the divided jets of `f`. -/
def hypertranscendentalJetFieldHom [CharZero F] : genericJetField F N →ₐ[F] E :=
  IsFractionRing.liftAlgHom (K := genericJetField F N)
    (hypertranscendentalJetLift_injective hf N)

theorem hypertranscendentalJetFieldHom_genericJetFieldMap [CharZero F] (z : genericJetAlgebra F N) :
    hypertranscendentalJetFieldHom hf N (genericJetFieldMap F N z) =
      hypertranscendentalJetLift hf N z := by
  rw [hypertranscendentalJetFieldHom, IsFractionRing.liftAlgHom_apply]
  exact IsFractionRing.lift_algebraMap (hypertranscendentalJetLift_injective hf N) z

theorem hypertranscendentalJetFieldHom_raw [CharZero F] {j : ℕ} (hj : j < N + 1) :
    hypertranscendentalJetFieldHom hf N (genericJetFieldMap F N (genericRaw F N j)) =
      dividedJet f j := by
  rw [hypertranscendentalJetFieldHom_genericJetFieldMap, hypertranscendentalJetLift_raw hf N hj]

theorem hypertranscendentalJetFieldHom_recip [CharZero F] {j : ℕ} (hj : j ≤ N) :
    hypertranscendentalJetFieldHom hf N (genericJetFieldMap F N (genericRecip F N j)) =
      dividedJet f⁻¹ j := by
  rw [hypertranscendentalJetFieldHom_genericJetFieldMap, hypertranscendentalJetLift_recip hf N hj]

end GenericPoint

section GaloisLaw

variable (F : Type*) [Field F] [Algebra F E]

/-- The finite divided-jet field `K_L = F(x_0,…,x_{L-1})`. -/
def dividedJetField (f : E) (L : ℕ) : IntermediateField F E :=
  IntermediateField.adjoin F (Set.range fun i : Fin L => dividedJet f i)

/-- The critical raw/reciprocal horizon coordinates `x_m,…,x_{L-1}, y_n,…,y_{L-1}`. -/
def criticalHorizonJet (f : E) (m n : ℕ) : Fin n ⊕ Fin m → E
  | Sum.inl i => dividedJet f (m + i)
  | Sum.inr j => dividedJet f⁻¹ (n + j)

/-- The critical raw/reciprocal horizon field `H_{m,n}`. -/
def criticalHorizonJetField (f : E) (m n : ℕ) : IntermediateField F E :=
  IntermediateField.adjoin F (Set.range (criticalHorizonJet f m n))

variable {F} [CharZero F] {f : E} (hf : HypertranscendentalOver F f) (m n : ℕ)
include hf

theorem hypertranscendentalJetFieldHom_comp_criticalAmbientRaw :
    hypertranscendentalJetFieldHom hf (m + n) ∘
        (fun j : Fin (m + n) => criticalAmbientRaw F m n (j : ℕ)) =
      fun j : Fin (m + n) => dividedJet f j := by
  funext j
  exact hypertranscendentalJetFieldHom_raw hf (m + n) (by omega)

theorem hypertranscendentalJetFieldHom_comp_criticalFieldObservation :
    hypertranscendentalJetFieldHom hf (m + n) ∘ criticalFieldObservation F m n =
      criticalHorizonJet f m n := by
  funext s
  rcases s with i | j
  · exact hypertranscendentalJetFieldHom_raw hf (m + n) (by omega)
  · exact hypertranscendentalJetFieldHom_recip hf (m + n) (by omega)

/-- The generic point carries the critical source field onto `K_L`. -/
theorem map_criticalSourceField_hypertranscendentalJetFieldHom :
    (criticalSourceField F m n).map (hypertranscendentalJetFieldHom hf (m + n)) =
      dividedJetField F f (m + n) := by
  rw [criticalSourceField, IntermediateField.adjoin_map, ← Set.range_comp,
    hypertranscendentalJetFieldHom_comp_criticalAmbientRaw]
  rfl

/-- The generic point carries the critical observation field onto `H_{m,n}`. -/
theorem map_criticalObservationField_hypertranscendentalJetFieldHom :
    (criticalObservationField F m n).map (hypertranscendentalJetFieldHom hf (m + n)) =
      criticalHorizonJetField F f m n := by
  rw [criticalObservationField, IntermediateField.adjoin_map, ← Set.range_comp,
    hypertranscendentalJetFieldHom_comp_criticalFieldObservation]
  rfl

/-- The critical horizon field lies in the finite divided-jet field. -/
theorem criticalHorizonJetField_le_dividedJetField :
    criticalHorizonJetField F f m n ≤ dividedJetField F f (m + n) := by
  rw [← map_criticalSourceField_hypertranscendentalJetFieldHom hf,
    ← map_criticalObservationField_hypertranscendentalJetFieldHom hf]
  exact IntermediateField.map_mono _ (criticalObservationField_le_criticalSourceField F)

/-- `K_L` as an extension of `H_{m,n}`. -/
abbrev criticalHorizonJetExtension : IntermediateField (criticalHorizonJetField F f m n) E :=
  IntermediateField.extendScalars (criticalHorizonJetField_le_dividedJetField hf m n)

/-- The generic point identifies the critical observation field with `H_{m,n}`. -/
def criticalObservationJetEquiv :
    criticalObservationField F m n ≃+* criticalHorizonJetField F f m n :=
  ((IntermediateField.equivMap (criticalObservationField F m n)
    (hypertranscendentalJetFieldHom hf (m + n))).trans
      (IntermediateField.equivOfEq
        (map_criticalObservationField_hypertranscendentalJetFieldHom hf m n))).toRingEquiv

/-- The generic point identifies the critical source field with `K_L` over `H_{m,n}`. -/
def criticalSourceJetEquiv :
    criticalSourceField F m n ≃+* criticalHorizonJetExtension hf m n :=
  (((IntermediateField.equivMap (criticalSourceField F m n)
    (hypertranscendentalJetFieldHom hf (m + n))).trans
      (IntermediateField.equivOfEq
        (map_criticalSourceField_hypertranscendentalJetFieldHom hf m n))).toRingEquiv).trans
    { toFun := fun z => ⟨z, z.2⟩
      invFun := fun z => ⟨z, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

theorem criticalJetEquiv_comp :
    (algebraMap (criticalHorizonJetField F f m n) (criticalHorizonJetExtension hf m n)).comp
        (criticalObservationJetEquiv hf m n).toRingHom =
      (criticalSourceJetEquiv hf m n).toRingHom.comp
        (algebraMap (criticalObservationField F m n) (criticalSourceField F m n)) := by
  ext z
  change hypertranscendentalJetFieldHom hf (m + n) (z : genericJetField F (m + n)) =
    hypertranscendentalJetFieldHom hf (m + n)
      ((algebraMap (criticalObservationField F m n) (criticalSourceField F m n) z :
        criticalSourceField F m n) : genericJetField F (m + n))
  rw [coe_algebraMap_criticalObservationSource]

theorem finrank_criticalHorizonJetExtension_eq_finrank :
    Module.finrank (criticalHorizonJetField F f m n) (criticalHorizonJetExtension hf m n) =
      Module.finrank (criticalObservationField F m n) (criticalSourceField F m n) :=
  (Algebra.finrank_eq_of_equiv_equiv (criticalObservationJetEquiv hf m n)
    (criticalSourceJetEquiv hf m n) (criticalJetEquiv_comp hf m n)).symm

/-- **The critical horizon degree.**  `[K_L : H_{m,n}] = choose(m+n, m)`. -/
theorem finrank_criticalHorizonJetExtension (hm : 0 < m) (hn : 0 < n) :
    Module.finrank (criticalHorizonJetField F f m n) (criticalHorizonJetExtension hf m n) =
      (m + n).choose m := by
  rw [finrank_criticalHorizonJetExtension_eq_finrank,
    finrank_criticalSourceField_eq_criticalHorizonMultiplicity_charZero F hm hn]
  rfl

theorem finiteDimensional_criticalHorizonJetExtension (hm : 0 < m) (hn : 0 < n) :
    FiniteDimensional (criticalHorizonJetField F f m n) (criticalHorizonJetExtension hf m n) :=
  Module.finite_of_finrank_pos (by
    rw [finrank_criticalHorizonJetExtension hf m n hm hn]
    exact Nat.choose_pos (by omega))

/-- **Full symmetric Galois ambiguity.**  The Galois group of the normal closure of
`K_L/H_{m,n}` acts on the `choose(m+n, m)` sheets as the full symmetric group. -/
theorem sheetAction_criticalHorizonJetExtension_bijective (hm : 0 < m) (hn : 0 < n) :
    Function.Bijective
      (sheetAction (criticalHorizonJetField F f m n) (criticalHorizonJetExtension hf m n)) := by
  haveI := criticalSourceField_finiteDimensional_criticalObservationField_charZero F hm hn
  haveI := finiteDimensional_criticalHorizonJetExtension hf m n hm hn
  haveI : CharZero (criticalObservationField F m n) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : CharZero (criticalHorizonJetField F f m n) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  exact (sheetAction_bijective_iff_of_ringEquiv (criticalObservationJetEquiv hf m n)
    (criticalSourceJetEquiv hf m n) (criticalJetEquiv_comp hf m n)).mp
      (sheetAction_criticalSourceField_bijective_charZero F hm hn)

/-- There are exactly `choose(m+n, m)` sheets. -/
theorem natCard_sheetEmbedding_criticalHorizonJetExtension (hm : 0 < m) (hn : 0 < n) :
    Nat.card (sheetEmbedding (criticalHorizonJetField F f m n)
      (criticalHorizonJetExtension hf m n)) = (m + n).choose m := by
  haveI := finiteDimensional_criticalHorizonJetExtension hf m n hm hn
  haveI : CharZero (criticalHorizonJetField F f m n) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  rw [natCard_sheetEmbedding, finrank_criticalHorizonJetExtension hf m n hm hn]

/-- **Atomicity.**  No field lies strictly between `H_{m,n}` and `K_L`. -/
theorem eq_or_eq_of_criticalHorizonJetField_le (hm : 0 < m) (hn : 0 < n)
    (M : IntermediateField F E) (h1 : criticalHorizonJetField F f m n ≤ M)
    (h2 : M ≤ dividedJetField F f (m + n)) :
    M = criticalHorizonJetField F f m n ∨ M = dividedJetField F f (m + n) := by
  haveI := finiteDimensional_criticalHorizonJetExtension hf m n hm hn
  haveI : CharZero (criticalHorizonJetField F f m n) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  set T := criticalHorizonJetExtension hf m n
  let M' : IntermediateField (criticalHorizonJetField F f m n) T :=
    (IntermediateField.extendScalars h1).comap T.val
  rcases eq_bot_or_eq_top_of_sheetAction_surjective _ _
      (sheetAction_criticalHorizonJetExtension_bijective hf m n hm hn).2 M' with hbot | htop
  · left
    apply le_antisymm _ h1
    intro x hx
    have hxM' : (⟨x, h2 hx⟩ : T) ∈ M' := hx
    rw [hbot, IntermediateField.mem_bot] at hxM'
    obtain ⟨c, hc⟩ := hxM'
    have hcx : (c : E) = x := congrArg Subtype.val hc
    rw [← hcx]
    exact c.2
  · right
    apply le_antisymm h2
    intro x hx
    have hxM' : (⟨x, hx⟩ : T) ∈ M' := by
      rw [htop]
      trivial
    exact hxM'

/-- **Radical threshold.**  Every element of `K_L` is solvable by radicals over `H_{m,n}` exactly
for the five pairs `(1,1), (1,2), (2,1), (1,3), (3,1)`. -/
theorem forall_mem_solvableByRad_criticalHorizonJetExtension_iff (hm : 0 < m) (hn : 0 < n) :
    (∀ x : criticalHorizonJetExtension hf m n,
      algebraMap (criticalHorizonJetExtension hf m n)
          (AlgebraicClosure (criticalHorizonJetExtension hf m n)) x ∈
        solvableByRad (criticalHorizonJetField F f m n)
          (AlgebraicClosure (criticalHorizonJetExtension hf m n))) ↔
      (m = 1 ∧ n = 1) ∨ (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) ∨ (m = 1 ∧ n = 3) ∨
        (m = 3 ∧ n = 1) := by
  haveI := finiteDimensional_criticalHorizonJetExtension hf m n hm hn
  haveI : CharZero (criticalHorizonJetField F f m n) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  rw [forall_isSolvableByRad_iff_finrank_le_four _ _
      (sheetAction_criticalHorizonJetExtension_bijective hf m n hm hn),
    finrank_criticalHorizonJetExtension hf m n hm hn]
  exact criticalHorizonMultiplicity_le_four_iff_mem hm hn

end GaloisLaw

section PageTransition

variable {F : Type*} [Field F] [Algebra F E]

omit [Differential E] in
/-- Scaling generators by nonzero constants does not change the field they generate. -/
theorem adjoin_range_smul_eq {ι : Type*} (u : ι → E) (c : ι → F) (hc : ∀ i, c i ≠ 0) :
    IntermediateField.adjoin F (Set.range fun i => c i • u i) =
      IntermediateField.adjoin F (Set.range u) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.smul_mem _ (IntermediateField.subset_adjoin F (Set.range u) ⟨i, rfl⟩)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    have hu : u i = (c i)⁻¹ • (c i • u i) := by
      rw [smul_smul, inv_mul_cancel₀ (hc i), one_smul]
    rw [hu]
    exact IntermediateField.smul_mem _
      (IntermediateField.subset_adjoin F (Set.range fun i => c i • u i) ⟨i, rfl⟩)

/-- The finite divided raw/reciprocal horizon `(y_b,…,y_N; x_a,…,x_N)`. -/
def finiteHorizonDividedJet (f : E) (a b N : ℕ) :
    Fin (finiteHorizonObservableCount N b) ⊕ Fin (finiteHorizonObservableCount N a) → E
  | Sum.inl i => dividedJet f⁻¹ (b + i)
  | Sum.inr i => dividedJet f (a + i)

variable (F) in
/-- The finite horizon field `O_{a,b;N} = F(x_a,…,x_N, y_b,…,y_N)`. -/
def finiteHorizonJetField (f : E) (a b N : ℕ) : IntermediateField F E :=
  IntermediateField.adjoin F (Set.range (finiteHorizonDividedJet f a b N))

theorem dividedJet_eq_smul [CharZero F] (x : E) (k : ℕ) :
    dividedJet x k = ((k.factorial : F))⁻¹ • differentialJet k x := by
  rw [dividedJet, Algebra.smul_def, map_inv₀, map_natCast, div_eq_inv_mul]

/-- Dividing by factorials does not change the finite horizon field. -/
theorem finiteHorizonJetField_eq_adjoin [CharZero F] (f : E) (a b N : ℕ) :
    finiteHorizonJetField F f a b N =
      IntermediateField.adjoin F (Set.range (finiteDifferentialHorizonObservation f a b N)) := by
  let c : Fin (finiteHorizonObservableCount N b) ⊕ Fin (finiteHorizonObservableCount N a) → F
    | Sum.inl i => (((b + i : ℕ).factorial : F))⁻¹
    | Sum.inr i => (((a + i : ℕ).factorial : F))⁻¹
  have hc : ∀ s, c s ≠ 0 := by
    rintro (i | i) <;> exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hfun : finiteHorizonDividedJet f a b N =
      fun s => c s • finiteDifferentialHorizonObservation f a b N s := by
    funext s
    rcases s with i | i <;> exact dividedJet_eq_smul _ _
  rw [finiteHorizonJetField, hfun, adjoin_range_smul_eq _ c hc]

/-- **The finite-jet Page law for a hypertranscendental source.**
`trdeg_F F(x_a,…,x_N, y_b,…,y_N) = min(N+1, (N+1-a) + (N+1-b))`. -/
theorem trdeg_finiteHorizonJetField [CharZero F] {f : E} (hf : HypertranscendentalOver F f)
    {a b N : ℕ} (ha : 0 < a) (haN : a ≤ N + 1) (hbN : b ≤ N + 1) :
    Algebra.trdeg F (finiteHorizonJetField F f a b N) =
      ((min (N + 1) ((N + 1 - a) + (N + 1 - b)) : ℕ) : Cardinal) := by
  rw [finiteHorizonJetField_eq_adjoin, trdeg_adjoin_range_eq_eRk_toNat]
  have h := finiteDifferentialHorizonObservationTranscendenceRank_eq (F := F) f hf ha haN hbN
  unfold finiteDifferentialHorizonObservationTranscendenceRank at h
  rw [h, finiteHorizonObservationRank_eq_min haN hbN]
  rfl

end PageTransition

end

end GaloisForLFunctions.HTGeometry
