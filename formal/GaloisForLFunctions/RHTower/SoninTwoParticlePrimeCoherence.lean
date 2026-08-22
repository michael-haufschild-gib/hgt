import GaloisForLFunctions.RHTower.TensorSquareCalkinLower
import GaloisForLFunctions.RHTower.SoninPrimeGramCompression

/-!
# Two-particle Sonin boundary energy

The corpus already owns the one-particle shell construction: contractive weakly-null inputs
`finitePairedEvenSoninInput`, their asymptotic orthonormality across scales through
`inverseDilatedEvenShellEven_orthonormal_scales_of_ratioSeparation`, and the scale-matrix limit
`evenCentralSoninDilationCorner_finitePairedInput_tendsto`.  Packaging those into a `ShellDatum`
and feeding it to `ShellDatum.tensor_calkin_lower` gives the card's tensor-square estimate:

`(∑_{(i,j)∈E} ‖d_{ij}‖²)^{1/2} ≤ ‖∑ d_{ij} (L_{r_i} ⊗ L_{r_j}) − K‖`

for every compact `K` on the Hilbert tensor square, and its Euler-normalized form with the weights
`1/(r_i r_j)`.  The shell parameters are chosen inside the proof by
`exists_finiteScale_gramSeparatingInteriorShell`, so the statements are unconditional.
-/

namespace RHTower

open Filter Topology UniformSpace
open scoped BigOperators TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 4000000

/-- The uniform-`ℂ`-action instance on the even Sonin tensor square, supplied directly so that the
completion of a tensor operator elaborates. -/
instance evenSoninTensorUniformContinuousConstSMul :
    UniformContinuousConstSMul ℂ (evenSubspace ⊗[ℂ] evenSubspace) :=
  tensorProduct_uniformContinuousConstSMul

/-- The normed group of the completed even Sonin tensor square. -/
noncomputable instance evenSoninTensorCompletionNormedAddCommGroup :
    NormedAddCommGroup (Completion (evenSubspace ⊗[ℂ] evenSubspace)) :=
  tensorCompletion_normedAddCommGroup

/-- The normed space structure of the completed even Sonin tensor square. -/
noncomputable instance evenSoninTensorCompletionNormedSpace :
    NormedSpace ℂ (Completion (evenSubspace ⊗[ℂ] evenSubspace)) :=
  tensorCompletion_normedSpace

noncomputable section

variable {n : ℕ}

/-- The Sonin shell datum of a finite family of distinct scales. -/
def soninShellDatum (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) (hinj : Function.Injective r)
    (harc : ∀ i, a < r i * c)
    (hout : ∀ i j, r i < r j → a * r i < c * r j)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex r,
      finiteActiveScaleRatio r z < finiteActiveScaleRatio r w →
        d * finiteActiveScaleRatio r z < c * finiteActiveScaleRatio r w)
    (i₀ : Fin n) :
    ShellDatum evenSubspace (Fin n) where
  L i := evenCentralSoninDilationCorner a (r i) (hr i)
  f i m := finitePairedEvenSoninInput a c d r hr hcd i m
  v m := finiteSoninRatioOutput c d r hr hcd i₀ i₀ m
  norm_f i m := norm_finitePairedEvenSoninInput_le_one a c d r hr hc hcd i m
  norm_v m := norm_finiteSoninRatioOutput_eq_one_of_le c d r hr hc hcd i₀ i₀ le_rfl m
  weak_f i l := finitePairedEvenSoninInput_weakly_tendsto_zero a c d r hr ha hc hcd harc i l
  inner_f := by
    intro i k
    have hshell : Orthonormal ℂ (fun j => inverseDilatedEvenShellEven c d (r j) hcd (hr j) 0) :=
      inverseDilatedEvenShellEven_orthonormal_scales_of_ratioSeparation c d r hr hinj hc hcd hsep 0
    have hconst : ∀ m : ℕ,
        inner ℂ (inverseDilatedEvenShellEven c d (r i) hcd (hr i) m)
            (inverseDilatedEvenShellEven c d (r k) hcd (hr k) m)
          = if i = k then (1 : ℂ) else 0 := by
      intro m
      have hm : Orthonormal ℂ (fun j => inverseDilatedEvenShellEven c d (r j) hcd (hr j) m) :=
        inverseDilatedEvenShellEven_orthonormal_scales_of_ratioSeparation c d r hr hinj hc hcd
          hsep m
      exact orthonormal_iff_ite.mp hm i k
    have hi : Tendsto (fun m => ‖finitePairedEvenSoninInput a c d r hr hcd i m -
        inverseDilatedEvenShellEven c d (r i) hcd (hr i) m‖) atTop (𝓝 0) := by
      simpa [finitePairedEvenSoninInput] using
        evenCentralSoninProjection_inverseDilatedEvenShell_tendsto a c d (r i) ha hc hcd (hr i)
          (harc i)
    have hk : Tendsto (fun m => ‖finitePairedEvenSoninInput a c d r hr hcd k m -
        inverseDilatedEvenShellEven c d (r k) hcd (hr k) m‖) atTop (𝓝 0) := by
      simpa [finitePairedEvenSoninInput] using
        evenCentralSoninProjection_inverseDilatedEvenShell_tendsto a c d (r k) ha hc hcd (hr k)
          (harc k)
    have hnorm : ∀ j, ∀ m, ‖inverseDilatedEvenShellEven c d (r j) hcd (hr j) m‖ ≤ 1 := by
      intro j m
      exact le_of_eq ((inverseDilatedEvenShellEven_orthonormal c d (r j) hc hcd (hr j)).norm_eq_one m)
    have hpair := norm_inner_sub_inner_tendsto_zero_of_paired_approx
      (hnorm i) (hnorm k) hi hk
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine hpair.congr fun m => ?_
    rw [hconst m]
  inner_Lf := by
    intro i j
    have hv : ∀ m, ‖finiteSoninRatioOutput c d r hr hcd i₀ i₀ m‖ ≤ 1 :=
      fun m => norm_finiteSoninRatioOutput_le_one c d r hr hc hcd i₀ i₀ m
    have hw : ∀ m, ‖finiteSoninRatioOutput c d r hr hcd j i m‖ ≤ 1 :=
      fun m => norm_finiteSoninRatioOutput_le_one c d r hr hc hcd j i m
    have hy := evenCentralSoninDilationCorner_finitePairedInput_tendsto a c d ha hc hcd hda r hr
      harc hout j i
    have hx : Tendsto (fun m : ℕ => ‖finiteSoninRatioOutput c d r hr hcd i₀ i₀ m -
        finiteSoninRatioOutput c d r hr hcd i₀ i₀ m‖) atTop (𝓝 0) := by
      simp
    have hpair := norm_inner_sub_inner_tendsto_zero_of_paired_approx hv hw hx hy
    have hconst : ∀ m : ℕ,
        inner ℂ (finiteSoninRatioOutput c d r hr hcd i₀ i₀ m)
            (finiteSoninRatioOutput c d r hr hcd j i m)
          = if i = j then (1 : ℂ) else 0 := by
      intro m
      by_cases hij : r i ≤ r j
      · rw [inner_finiteSoninRatioOutput_active c d r hr hc hcd hsep j i i₀ i₀ hij le_rfl m]
        have hri0 : r i ≠ 0 := (zero_lt_one.trans (hr i)).ne'
        have hri00 : r i₀ ≠ 0 := (zero_lt_one.trans (hr i₀)).ne'
        rw [div_self hri00]
        by_cases hEq : i = j
        · subst hEq
          simp [div_self hri0]
        · have hne : r j / r i ≠ 1 := by
            intro hone
            exact hEq (hinj ((div_eq_one_iff_eq hri0).mp hone).symm)
          rw [if_neg (fun hcon => hne hcon.symm), if_neg hEq]
      · have hzero : finiteSoninRatioOutput c d r hr hcd j i m = 0 := by
          rw [finiteSoninRatioOutput, dif_neg hij]
        have hEq : i ≠ j := by
          intro hcon
          exact hij (le_of_eq (congrArg r hcon))
        rw [hzero, inner_zero_right, if_neg hEq]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine hpair.congr fun m => ?_
    rw [hconst m]

/-- **Card `(2)`: on the tensor square of the actual even Sonin carrier, the finite ordered pair
section retains the full weighted coefficient energy modulo compact operators.**  The shell
parameters are chosen inside the proof, so the statement is unconditional. -/
theorem sonin_tensor_calkin_lower (a : ℝ) (ha : 0 < a) (r : Fin n → ℝ)
    (hr : ∀ i, 1 < r i) (hinj : Function.Injective r) (dd : Fin n × Fin n → ℂ)
    (K : Completion (evenSubspace ⊗[ℂ] evenSubspace) →L[ℂ]
      Completion (evenSubspace ⊗[ℂ] evenSubspace)) (hK : IsCompactOperator K) :
    Real.sqrt (∑ α : Fin n × Fin n, ‖dd α‖ ^ 2) ≤
      ‖(∑ α : Fin n × Fin n, TensorProduct.mapL
          (dd α • evenCentralSoninDilationCorner a (r α.1) (hr α.1))
          (evenCentralSoninDilationCorner a (r α.2) (hr α.2))).completion - K‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : (∑ α : Fin 0 × Fin 0, ‖dd α‖ ^ 2) = 0 := by simp
    rw [hzero, Real.sqrt_zero]
    exact norm_nonneg _
  · haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    obtain ⟨c, d, hc, hcd, hda, harc, hout, hsep⟩ :=
      exists_finiteScale_gramSeparatingInteriorShell a ha r hr
    exact (soninShellDatum a c d ha hc hcd hda r hr hinj harc hout hsep
      (Classical.arbitrary (Fin n))).tensor_calkin_lower dd K hK

/-- **Card `(1)`: the same estimate for the positive Euler-normalized corners
`C_r = -r^{-1/2} L_r`, whose coefficient energy carries the reciprocal-scale weights
`1/(r_i r_j)`.** -/
theorem sonin_euler_tensor_calkin_lower (a : ℝ) (ha : 0 < a) (r : Fin n → ℝ)
    (hr : ∀ i, 1 < r i) (hinj : Function.Injective r) (b : Fin n × Fin n → ℂ)
    (K : Completion (evenSubspace ⊗[ℂ] evenSubspace) →L[ℂ]
      Completion (evenSubspace ⊗[ℂ] evenSubspace)) (hK : IsCompactOperator K) :
    Real.sqrt (∑ α : Fin n × Fin n, ‖b α‖ ^ 2 / (r α.1 * r α.2)) ≤
      ‖(∑ α : Fin n × Fin n, TensorProduct.mapL
          ((b α * (-((Real.sqrt (r α.1) : ℂ))⁻¹)) •
            evenCentralSoninDilationCorner a (r α.1) (hr α.1))
          ((-((Real.sqrt (r α.2) : ℂ))⁻¹) •
            evenCentralSoninDilationCorner a (r α.2) (hr α.2))).completion - K‖ := by
  have hpos : ∀ i, 0 < r i := fun i => zero_lt_one.trans (hr i)
  have hsqrtpos : ∀ i, 0 < Real.sqrt (r i) := fun i => Real.sqrt_pos.mpr (hpos i)
  set dd : Fin n × Fin n → ℂ := fun α =>
    b α * (-((Real.sqrt (r α.1) : ℂ))⁻¹) * (-((Real.sqrt (r α.2) : ℂ))⁻¹) with hdd
  have hop : (∑ α : Fin n × Fin n, TensorProduct.mapL
        ((b α * (-((Real.sqrt (r α.1) : ℂ))⁻¹)) •
          evenCentralSoninDilationCorner a (r α.1) (hr α.1))
        ((-((Real.sqrt (r α.2) : ℂ))⁻¹) •
          evenCentralSoninDilationCorner a (r α.2) (hr α.2)))
      = ∑ α : Fin n × Fin n, TensorProduct.mapL
          (dd α • evenCentralSoninDilationCorner a (r α.1) (hr α.1))
          (evenCentralSoninDilationCorner a (r α.2) (hr α.2)) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mapL_smul_smul, hdd]
  have hnormsq : ∀ α : Fin n × Fin n, ‖dd α‖ ^ 2 = ‖b α‖ ^ 2 / (r α.1 * r α.2) := by
    intro α
    rw [hdd]
    simp only [norm_mul, norm_neg, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt (hpos α.1).le,
      Real.sq_sqrt (hpos α.2).le]
    field_simp
  rw [hop, ← Finset.sum_congr rfl fun α _ => hnormsq α]
  exact sonin_tensor_calkin_lower a ha r hr hinj dd K hK

/-- Every prime exceeds one as a real scale. -/
theorem one_lt_prime_real (p : Nat.Primes) : (1 : ℝ) < (p : ℝ) := by
  exact_mod_cast p.prop.one_lt

/-- The positive Euler-normalized even Sonin corner `C_r = -r^{-1/2} L_r`. -/
def evenPositiveEulerSoninCorner (t r : ℝ) (hr : 1 < r) : evenSubspace →L[ℂ] evenSubspace :=
  (-((Real.sqrt r : ℂ))⁻¹) • evenCentralSoninDilationCorner t r hr

/-- `(7)`: the finite ordered prime coboundary section
`T_F(u) = ∑_{p,q ∈ F} (u_p − u_q) (C_p ⊗ C_q)` on the completed even Sonin tensor square. -/
def soninPrimePairSection (t : ℝ) (u : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    Completion (evenSubspace ⊗[ℂ] evenSubspace) →L[ℂ]
      Completion (evenSubspace ⊗[ℂ] evenSubspace) :=
  (∑ p ∈ s, ∑ q ∈ s, TensorProduct.mapL
    ((u p - u q) • evenPositiveEulerSoninCorner t (p : ℝ) (one_lt_prime_real p))
    (evenPositiveEulerSoninCorner t (q : ℝ) (one_lt_prime_real q))).completion

/-- Reindexing a double sum over a finite prime set through the canonical enumeration of the set. -/
theorem sum_fin_card_eq_sum_prime_pairs {M : Type*} [AddCommMonoid M]
    (s : Finset Nat.Primes) (f : Nat.Primes → Nat.Primes → M) :
    (∑ α : Fin s.card × Fin s.card,
        f ((s.equivFin.symm α.1 : {x // x ∈ s}) : Nat.Primes)
          ((s.equivFin.symm α.2 : {x // x ∈ s}) : Nat.Primes)) =
      ∑ p ∈ s, ∑ q ∈ s, f p q := by
  classical
  rw [Fintype.sum_prod_type]
  have hinner : ∀ x : Nat.Primes,
      (∑ j : Fin s.card, f x ((s.equivFin.symm j : {y // y ∈ s}) : Nat.Primes)) =
        ∑ q ∈ s, f x q := by
    intro x
    rw [Equiv.sum_comp s.equivFin.symm (fun y : {y // y ∈ s} => f x (y : Nat.Primes)),
      Finset.univ_eq_attach, Finset.sum_attach s (fun q => f x q)]
  simp_rw [hinner]
  rw [Equiv.sum_comp s.equivFin.symm
      (fun y : {y // y ∈ s} => ∑ q ∈ s, f (y : Nat.Primes) q),
    Finset.univ_eq_attach, Finset.sum_attach s (fun p => ∑ q ∈ s, f p q)]

/-- `(4)`--`(5)`: the reciprocal-prime pair energy of a prime potential is dominated by the Calkin
norm of its finite ordered prime pair section. -/
theorem sqrt_primePairDifferenceEnergy_le_norm_soninPrimePairSection_sub_compact
    (t : ℝ) (ht : 0 < t) (u : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (K : Completion (evenSubspace ⊗[ℂ] evenSubspace) →L[ℂ]
      Completion (evenSubspace ⊗[ℂ] evenSubspace)) (hK : IsCompactOperator K) :
    Real.sqrt (primePairDifferenceEnergy u s) ≤ ‖soninPrimePairSection t u s - K‖ := by
  classical
  set e : Fin s.card ≃ {x // x ∈ s} := s.equivFin.symm with he
  set r : Fin s.card → ℝ := fun i => (((e i : {x // x ∈ s}) : Nat.Primes) : ℝ) with hrdef
  have hr : ∀ i, 1 < r i := fun i => one_lt_prime_real _
  have hinj : Function.Injective r := by
    intro i j hij
    have hreal : (((e i : {x // x ∈ s}) : Nat.Primes) : ℝ)
        = (((e j : {x // x ∈ s}) : Nat.Primes) : ℝ) := hij
    have hnat : (((e i : {x // x ∈ s}) : Nat.Primes) : ℕ)
        = (((e j : {x // x ∈ s}) : Nat.Primes) : ℕ) := by
      exact_mod_cast hreal
    exact e.injective (Subtype.ext (Subtype.ext hnat))
  set b : Fin s.card × Fin s.card → ℂ := fun α =>
    u ((e α.1 : {x // x ∈ s}) : Nat.Primes) - u ((e α.2 : {x // x ∈ s}) : Nat.Primes) with hbdef
  have hop : soninPrimePairSection t u s =
      (∑ α : Fin s.card × Fin s.card, TensorProduct.mapL
        ((b α * (-((Real.sqrt (r α.1) : ℂ))⁻¹)) •
          evenCentralSoninDilationCorner t (r α.1) (hr α.1))
        ((-((Real.sqrt (r α.2) : ℂ))⁻¹) •
          evenCentralSoninDilationCorner t (r α.2) (hr α.2))).completion := by
    rw [soninPrimePairSection]
    congr 1
    rw [← sum_fin_card_eq_sum_prime_pairs s (fun p q => TensorProduct.mapL
      ((u p - u q) • evenPositiveEulerSoninCorner t (p : ℝ) (one_lt_prime_real p))
      (evenPositiveEulerSoninCorner t (q : ℝ) (one_lt_prime_real q)))]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [evenPositiveEulerSoninCorner, evenPositiveEulerSoninCorner, smul_smul]
  have henergy : primePairDifferenceEnergy u s =
      ∑ α : Fin s.card × Fin s.card, ‖b α‖ ^ 2 / (r α.1 * r α.2) := by
    rw [sum_fin_card_eq_sum_prime_pairs s
      (fun p q => ‖u p - u q‖ ^ 2 / ((p : ℝ) * (q : ℝ)))]
    rw [primePairDifferenceEnergy]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [primePairDifferenceRow, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [div_div, mul_comm ((q : ℝ)) ((p : ℝ))]
  have hkey := sonin_euler_tensor_calkin_lower t ht r hr hinj b K hK
  rw [← hop] at hkey
  rw [← henergy] at hkey
  exact hkey

/-- `(9)`: one Calkin bound on a finite ordered prime pair section bounds the reciprocal-prime
pair energy of the potential on that set. -/
theorem primePairDifferenceEnergy_le_of_calkin_le (t : ℝ) (ht : 0 < t) (u : Nat.Primes → ℂ)
    (B : ℝ) (s : Finset Nat.Primes)
    (K : Completion (evenSubspace ⊗[ℂ] evenSubspace) →L[ℂ]
      Completion (evenSubspace ⊗[ℂ] evenSubspace)) (hK : IsCompactOperator K)
    (hle : ‖soninPrimePairSection t u s - K‖ ≤ B) :
    primePairDifferenceEnergy u s ≤ B ^ 2 := by
  have hkey :=
    sqrt_primePairDifferenceEnergy_le_norm_soninPrimePairSection_sub_compact t ht u s K hK
  have hE0 : 0 ≤ primePairDifferenceEnergy u s := primePairDifferenceEnergy_nonneg u s
  have hsq := Real.sq_sqrt hE0
  have hnn := Real.sqrt_nonneg (primePairDifferenceEnergy u s)
  nlinarith [hkey.trans hle]

/-- **Card prime-coherence theorem `(8) ⟹` constancy.**  If the finite ordered prime coboundary
sections of a prime potential are uniformly bounded modulo compact operators on the even Sonin
tensor square, then the potential is constant. -/
theorem sonin_prime_pair_calkin_bounded_imp_constant (t : ℝ) (ht : 0 < t) (u : Nat.Primes → ℂ)
    (hbdd : ∃ B : ℝ, ∀ s : Finset Nat.Primes,
      ∃ K : Completion (evenSubspace ⊗[ℂ] evenSubspace) →L[ℂ]
        Completion (evenSubspace ⊗[ℂ] evenSubspace),
        IsCompactOperator K ∧ ‖soninPrimePairSection t u s - K‖ ≤ B) :
    ∃ c : ℂ, ∀ p, u p = c := by
  obtain ⟨B, hB⟩ := hbdd
  refine (primePairDifferenceEnergyBounded_iff_constant u).mp ⟨B ^ 2, fun s => ?_⟩
  obtain ⟨K, hK, hle⟩ := hB s
  exact primePairDifferenceEnergy_le_of_calkin_le t ht u B s K hK hle

end

end RHTower
