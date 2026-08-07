import GaloisForLFunctions.HTGeometry.CriticalBiprojectiveBoundary
import GaloisForLFunctions.HTGeometry.LaurentSeriesNormalization
import GaloisForLFunctions.HTGeometry.PowerSeriesCriticalDeformation

/-!
# Integrality of the one-parameter critical fibre

The critical fibre over a Laurent-series field has no points outside the power-series lattice.
The proof normalizes both coefficient blocks projectively.  Reduction modulo the uniformizer would
produce a point on the boundary of the pure critical biprojective fibre unless both affine
coordinates remained nonzero.  Boundary exclusion therefore forces every Laurent coefficient to
be integral.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped LaurentSeries

/-! ## Base change of critical fibres -/

/-- Critical compatibility is functorial under scalar extension. -/
noncomputable def criticalFibreMap
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (m n : ℕ) (U V : R[X]) :
    criticalFibre R m n U V →
      criticalFibre S m n (U.map f) (V.map f) := fun p =>
  ⟨(p.1.1.map f, p.1.2.map f),
    lt_of_le_of_lt Polynomial.degree_map_le p.2.1,
    lt_of_le_of_lt Polynomial.degree_map_le p.2.2.1, by
      have h := Polynomial.map_dvd f p.2.2.2
      simpa [criticalLowProduct] using h⟩

theorem criticalFibreMap_injective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (m n : ℕ) (U V : R[X]) :
    Function.Injective (criticalFibreMap f m n U V) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · apply Polynomial.map_injective f hf
    exact congrArg (fun z => z.1.1) hpq
  · apply Polynomial.map_injective f hf
    exact congrArg (fun z => z.1.2) hpq

theorem powerSeriesToLaurent_injective (E : Type*) [Field E] :
    Function.Injective (algebraMap (PowerSeries E) E⸨X⸩) :=
  HahnSeries.ofPowerSeries_injective (Γ := ℤ)

noncomputable def powerSeriesCriticalFibreToLaurent
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) (v : Fin m → E) :
    criticalFibre (PowerSeries E) m n
        (X ^ m + powerSeriesRawDeformation E m n u)
        (X ^ n + powerSeriesReciprocalDeformation E m n v) →
      criticalFibre E⸨X⸩ m n
        ((X ^ m + powerSeriesRawDeformation E m n u).map
          (algebraMap (PowerSeries E) E⸨X⸩))
        ((X ^ n + powerSeriesReciprocalDeformation E m n v).map
          (algebraMap (PowerSeries E) E⸨X⸩)) :=
  criticalFibreMap (algebraMap (PowerSeries E) E⸨X⸩) m n _ _

theorem powerSeriesCriticalFibreToLaurent_injective
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) (v : Fin m → E) :
    Function.Injective (powerSeriesCriticalFibreToLaurent E m n u v) :=
  criticalFibreMap_injective _ (powerSeriesToLaurent_injective E) m n _ _

/-! ## Finite coefficient blocks -/

/-- Polynomial represented by a finite low-coefficient vector. -/
noncomputable def lowPolynomial
    {R : Type*} [Semiring R] {d : ℕ} (a : Fin d → R) : R[X] :=
  ∑ i : Fin d, C (a i) * X ^ (i : ℕ)

theorem lowPolynomial_coeff
    {R : Type*} [Semiring R] {d k : ℕ} (a : Fin d → R) :
    (lowPolynomial a).coeff k = if h : k < d then a ⟨k, h⟩ else 0 := by
  classical
  rw [lowPolynomial, Polynomial.finsetSum_coeff]
  split_ifs with hk
  · rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin d)]
    · simp
    · intro i _ hi
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      exact fun h => hi (Fin.ext h.symm)
    · exact fun h => absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hk (h ▸ i.2)

theorem lowPolynomial_degree_lt
    {R : Type*} [Semiring R] {d : ℕ} (a : Fin d → R) :
    (lowPolynomial a).degree < (d : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  rw [lowPolynomial_coeff, dif_neg (Nat.not_lt_of_ge hk)]

theorem map_lowPolynomial
    {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {d : ℕ} (a : Fin d → R) :
    (lowPolynomial a).map f = lowPolynomial (fun i => f (a i)) := by
  rw [lowPolynomial, lowPolynomial, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- Low coefficients followed by the affine coordinate `1`. -/
def affineBlockCoordinates
    {R : Type*} [Semiring R] {d : ℕ} (A : R[X]) : Fin d ⊕ Unit → R
  | Sum.inl i => A.coeff i
  | Sum.inr _ => 1

@[simp] theorem affineBlockCoordinates_low
    {R : Type*} [Semiring R] {d : ℕ} (A : R[X]) (i : Fin d) :
    affineBlockCoordinates A (Sum.inl i) = A.coeff i := rfl

@[simp] theorem affineBlockCoordinates_infinity
    {R : Type*} [Semiring R] {d : ℕ} (A : R[X]) :
    affineBlockCoordinates (d := d) A (Sum.inr ()) = 1 := rfl

/-- A normalized integral coefficient block maps to the inverse-scale multiple of its original
Laurent polynomial. -/
theorem map_normalizedLowPolynomial
    (E : Type*) [Field E] {d : ℕ} {A : E⸨X⸩[X]}
    (hA : A.degree < (d : ℕ)) {c : E⸨X⸩}
    {w : Fin d ⊕ Unit → PowerSeries E}
    (hw : ∀ i, (w i : E⸨X⸩) = affineBlockCoordinates A i / c) :
    (lowPolynomial (fun i => w (Sum.inl i))).map
        (algebraMap (PowerSeries E) E⸨X⸩) = C c⁻¹ * A := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < d
  · rw [Polynomial.coeff_map, lowPolynomial_coeff, dif_pos hk,
      Polynomial.coeff_C_mul]
    simpa [div_eq_mul_inv, mul_comm] using hw (Sum.inl (⟨k, hk⟩ : Fin d))
  · rw [Polynomial.coeff_map, lowPolynomial_coeff, dif_neg hk,
      map_zero, Polynomial.coeff_C_mul]
    have hAk : A.coeff k = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero A d).mp hA k (Nat.le_of_not_gt hk)
    rw [hAk, mul_zero]

/-- Separately homogeneous critical defect used by projective normalization. -/
noncomputable def homogeneousCriticalDefect
    {R : Type*} [CommRing R] (U V A B : R[X]) (α β : R) : R[X] :=
  (A + C α * U) * (B + C β * V) - C (α * β)

theorem homogeneousCriticalDefect_eq
    {R : Type*} [CommRing R] (U V A B : R[X]) (α β : R) :
    homogeneousCriticalDefect U V A B α β =
      A * B + A * (C β * V) + (C α * U) * B +
        C (α * β) * (U * V) - C (α * β) := by
  rw [homogeneousCriticalDefect]
  rw [map_mul]
  ring

/-- The homogeneous defect below the critical horizon; the tail-tail term is absent because it is
already divisible by the horizon. -/
noncomputable def homogeneousTruncatedCriticalDefect
    {R : Type*} [CommRing R] (U V A B : R[X]) (α β : R) : R[X] :=
  A * B + A * (C β * V) + (C α * U) * B - C (α * β)

/-! ## Valuative boundary argument -/

/-- Every coefficient of a Laurent critical-fibre point in the one-parameter deformation is
integral.  This is the valuative criterion in explicit coefficient form. -/
theorem powerSeriesCriticalFibre_laurent_coefficients_integral
    (E : Type*) [Field E] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (u : Fin n → E) (v : Fin m → E)
    (p : criticalFibre E⸨X⸩ m n
      ((X ^ m + powerSeriesRawDeformation E m n u).map
        (algebraMap (PowerSeries E) E⸨X⸩))
      ((X ^ n + powerSeriesReciprocalDeformation E m n v).map
        (algebraMap (PowerSeries E) E⸨X⸩))) :
    (∀ i : Fin m, Valued.v (p.1.1.coeff i) ≤ 1) ∧
      ∀ j : Fin n, Valued.v (p.1.2.coeff j) ≤ 1 := by
  classical
  let ι : PowerSeries E →+* E⸨X⸩ := algebraMap (PowerSeries E) E⸨X⸩
  let ε : PowerSeries E →+* E := PowerSeries.constantCoeff
  let US : (PowerSeries E)[X] := X ^ m + powerSeriesRawDeformation E m n u
  let VS : (PowerSeries E)[X] := X ^ n + powerSeriesReciprocalDeformation E m n v
  let U : E⸨X⸩[X] := US.map ι
  let V : E⸨X⸩[X] := VS.map ι
  let A : E⸨X⸩[X] := p.1.1
  let B : E⸨X⸩[X] := p.1.2
  let xA : Fin m ⊕ Unit → E⸨X⸩ := affineBlockCoordinates A
  let xB : Fin n ⊕ Unit → E⸨X⸩ := affineBlockCoordinates B
  obtain ⟨c, hc, wA, iA, _hiAc, hmaxA, hwA, hwiA⟩ :=
    exists_laurent_powerSeries_normalization E xA ⟨Sum.inr (), rfl⟩
  obtain ⟨d, hd, wB, iB, _hiBd, hmaxB, hwB, hwiB⟩ :=
    exists_laurent_powerSeries_normalization E xB ⟨Sum.inr (), rfl⟩
  let Abar : (PowerSeries E)[X] := lowPolynomial (fun i => wA (Sum.inl i))
  let Bbar : (PowerSeries E)[X] := lowPolynomial (fun j => wB (Sum.inl j))
  let α : PowerSeries E := wA (Sum.inr ())
  let β : PowerSeries E := wB (Sum.inr ())
  have hmapA : Abar.map ι = C c⁻¹ * A := by
    exact map_normalizedLowPolynomial E p.2.1 hwA
  have hmapB : Bbar.map ι = C d⁻¹ * B := by
    exact map_normalizedLowPolynomial E p.2.2.1 hwB
  have hmapα : ι α = c⁻¹ := by
    change (α : E⸨X⸩) = c⁻¹
    simpa [α, xA, affineBlockCoordinates] using hwA (Sum.inr ())
  have hmapβ : ι β = d⁻¹ := by
    change (β : E⸨X⸩) = d⁻¹
    simpa [β, xB, affineBlockCoordinates] using hwB (Sum.inr ())
  let H : (PowerSeries E)[X] :=
    homogeneousTruncatedCriticalDefect US VS Abar Bbar α β
  have hmapH : H.map ι = C (c * d)⁻¹ * (criticalLowProduct U V A B - 1) := by
    dsimp only [H, homogeneousTruncatedCriticalDefect]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    rw [hmapA, hmapB, hmapα, hmapβ]
    rw [map_mul, hmapα, hmapβ]
    dsimp only [U, V]
    rw [show (c * d)⁻¹ = c⁻¹ * d⁻¹ by ring_nf]
    simp only [criticalLowProduct]
    simp only [map_mul]
    ring
  have hmapHdvd : (X : E⸨X⸩[X]) ^ (m + n) ∣ H.map ι := by
    rw [hmapH]
    exact dvd_mul_of_dvd_right p.2.2.2 _
  have hHdvd : (X : (PowerSeries E)[X]) ^ (m + n) ∣ H := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    apply powerSeriesToLaurent_injective E
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp hmapHdvd) k hk
    simpa [ι] using hcoeff
  have hUS : US.map ε = (X : E[X]) ^ m := by
    have hraw : (powerSeriesRawDeformation E m n u).map ε = 0 := by
      rw [powerSeriesRawDeformation, Polynomial.map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [powerSeriesDeformParam, ε]
    dsimp only [US]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, hraw, add_zero]
  have hVS : VS.map ε = (X : E[X]) ^ n := by
    have hrecip : (powerSeriesReciprocalDeformation E m n v).map ε = 0 := by
      rw [powerSeriesReciprocalDeformation, Polynomial.map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [powerSeriesDeformParam, ε]
    dsimp only [VS]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, hrecip, add_zero]
  let A0 : E[X] := Abar.map ε
  let B0 : E[X] := Bbar.map ε
  let α0 : E := ε α
  let β0 : E := ε β
  have htrunc0 : (X : E[X]) ^ (m + n) ∣
      homogeneousTruncatedCriticalDefect (X ^ m) (X ^ n) A0 B0 α0 β0 := by
    have h := Polynomial.map_dvd ε hHdvd
    simpa [H, homogeneousTruncatedCriticalDefect, A0, B0, α0, β0, hUS, hVS] using h
  have hboundary : (X : E[X]) ^ (m + n) ∣
      homogeneousCriticalDefect (X ^ m) (X ^ n) A0 B0 α0 β0 := by
    have hextra : (X : E[X]) ^ (m + n) ∣ C (α0 * β0) * X ^ (m + n) := by
      exact dvd_mul_left _ _
    rw [homogeneousCriticalDefect_eq]
    have hid :
        A0 * B0 + A0 * (C β0 * X ^ n) + (C α0 * X ^ m) * B0 +
              C (α0 * β0) * (X ^ m * X ^ n) - C (α0 * β0) =
          homogeneousTruncatedCriticalDefect (X ^ m) (X ^ n) A0 B0 α0 β0 +
            C (α0 * β0) * X ^ (m + n) := by
      rw [homogeneousTruncatedCriticalDefect, pow_add]
      ring
    rw [hid]
    exact dvd_add htrunc0 hextra
  have hA0deg : A0.natDegree < m := by
    by_cases hA0 : A0 = 0
    · simpa [hA0] using hm
    · exact (Polynomial.natDegree_lt_iff_degree_lt hA0).2
        (lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _))
  have hB0deg : B0.natDegree < n := by
    by_cases hB0 : B0 = 0
    · simpa [hB0] using hn
    · exact (Polynomial.natDegree_lt_iff_degree_lt hB0).2
        (lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _))
  have hleft : A0 ≠ 0 ∨ α0 ≠ 0 := by
    rcases iA with i | q
    · left
      intro hzero
      have hcoeff : A0.coeff i = 1 := by
        simp [A0, Abar, lowPolynomial_coeff, hwiA]
      simp [hzero] at hcoeff
    · right
      intro hzero
      have hone : α0 = 1 := by
        simpa [α0, α] using congrArg ε hwiA
      exact zero_ne_one (hzero ▸ hone)
  have hright : B0 ≠ 0 ∨ β0 ≠ 0 := by
    rcases iB with j | q
    · left
      intro hzero
      have hcoeff : B0.coeff j = 1 := by
        simp [B0, Bbar, lowPolynomial_coeff, hwiB]
      simp [hzero] at hcoeff
    · right
      intro hzero
      have hone : β0 = 1 := by
        simpa [β0, β] using congrArg ε hwiB
      exact zero_ne_one (hzero ▸ hone)
  have hinfinity := critical_biprojective_boundary_exclusion hA0deg hB0deg hleft hright
    (by simpa [homogeneousCriticalDefect] using hboundary)
  have hvalA : ∀ i, Valued.v (xA i) ≤ 1 :=
    laurent_all_val_le_one_of_normalized_coordinate E
      (a := Sum.inr ()) rfl hc hmaxA hwA hinfinity.1
  have hvalB : ∀ i, Valued.v (xB i) ≤ 1 :=
    laurent_all_val_le_one_of_normalized_coordinate E
      (a := Sum.inr ()) rfl hd hmaxB hwB hinfinity.2
  exact ⟨fun i => hvalA (Sum.inl i), fun j => hvalB (Sum.inl j)⟩

/-! ## Descent of points and exact Laurent count -/

/-- Chosen power-series representative of an integral Laurent series. -/
noncomputable def laurentIntegralLift
    (E : Type*) [Field E] (f : E⸨X⸩) (hf : Valued.v f ≤ 1) : PowerSeries E :=
  Classical.choose ((LaurentSeries.val_le_one_iff_eq_coe E f).mp hf)

@[simp] theorem coe_laurentIntegralLift
    (E : Type*) [Field E] (f : E⸨X⸩) (hf : Valued.v f ≤ 1) :
    (laurentIntegralLift E f hf : E⸨X⸩) = f :=
  Classical.choose_spec ((LaurentSeries.val_le_one_iff_eq_coe E f).mp hf)

theorem map_integralLowPolynomial_eq
    (E : Type*) [Field E] {d : ℕ} {A : E⸨X⸩[X]}
    (hAdeg : A.degree < (d : ℕ))
    (hAint : ∀ i : Fin d, Valued.v (A.coeff i) ≤ 1) :
    (lowPolynomial (fun i => laurentIntegralLift E (A.coeff i) (hAint i))).map
        (algebraMap (PowerSeries E) E⸨X⸩) = A := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < d
  · rw [Polynomial.coeff_map, lowPolynomial_coeff, dif_pos hk]
    exact coe_laurentIntegralLift E _ _
  · rw [Polynomial.coeff_map, lowPolynomial_coeff, dif_neg hk, map_zero]
    exact ((Polynomial.degree_lt_iff_coeff_zero A d).mp hAdeg k (Nat.le_of_not_gt hk)).symm

theorem powerSeriesCriticalFibreToLaurent_surjective
    (E : Type*) [Field E] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (u : Fin n → E) (v : Fin m → E) :
    Function.Surjective (powerSeriesCriticalFibreToLaurent E m n u v) := by
  classical
  intro p
  obtain ⟨hAint, hBint⟩ :=
    powerSeriesCriticalFibre_laurent_coefficients_integral E hm hn u v p
  let Ahat : (PowerSeries E)[X] :=
    lowPolynomial (fun i => laurentIntegralLift E (p.1.1.coeff i) (hAint i))
  let Bhat : (PowerSeries E)[X] :=
    lowPolynomial (fun j => laurentIntegralLift E (p.1.2.coeff j) (hBint j))
  let ι : PowerSeries E →+* E⸨X⸩ := algebraMap (PowerSeries E) E⸨X⸩
  let US : (PowerSeries E)[X] := X ^ m + powerSeriesRawDeformation E m n u
  let VS : (PowerSeries E)[X] := X ^ n + powerSeriesReciprocalDeformation E m n v
  have hmapA : Ahat.map ι = p.1.1 := by
    exact map_integralLowPolynomial_eq E p.2.1 hAint
  have hmapB : Bhat.map ι = p.1.2 := by
    exact map_integralLowPolynomial_eq E p.2.2.1 hBint
  have hmapDefect :
      (criticalLowProduct US VS Ahat Bhat - 1).map ι =
        criticalLowProduct (US.map ι) (VS.map ι) p.1.1 p.1.2 - 1 := by
    simp only [criticalLowProduct, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_one, hmapA, hmapB]
  have hdvd : (X : (PowerSeries E)[X]) ^ (m + n) ∣
      criticalLowProduct US VS Ahat Bhat - 1 := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    apply powerSeriesToLaurent_injective E
    have hp := (Polynomial.X_pow_dvd_iff.mp p.2.2.2) k hk
    have hcoeff := congrArg (fun P : E⸨X⸩[X] => P.coeff k) hmapDefect
    rw [Polynomial.coeff_map] at hcoeff
    rw [hcoeff]
    simpa [ι, US, VS] using hp
  let q : criticalFibre (PowerSeries E) m n US VS :=
    ⟨(Ahat, Bhat), lowPolynomial_degree_lt _, lowPolynomial_degree_lt _, hdvd⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hmapA
  · exact hmapB

/-- Power-series and Laurent-series critical fibres coincide point-for-point. -/
noncomputable def powerSeriesCriticalFibreLaurentEquiv
    (E : Type*) [Field E] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (u : Fin n → E) (v : Fin m → E) :
    criticalFibre (PowerSeries E) m n
        (X ^ m + powerSeriesRawDeformation E m n u)
        (X ^ n + powerSeriesReciprocalDeformation E m n v) ≃
      criticalFibre E⸨X⸩ m n
        ((X ^ m + powerSeriesRawDeformation E m n u).map
          (algebraMap (PowerSeries E) E⸨X⸩))
        ((X ^ n + powerSeriesReciprocalDeformation E m n v).map
          (algebraMap (PowerSeries E) E⸨X⸩)) :=
  Equiv.ofBijective (powerSeriesCriticalFibreToLaurent E m n u v)
    ⟨powerSeriesCriticalFibreToLaurent_injective E m n u v,
      powerSeriesCriticalFibreToLaurent_surjective E hm hn u v⟩

/-- Exact critical multiplicity over the Laurent-series generic direction. -/
theorem nat_card_laurentSeriesCriticalFibre
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (u : Fin n → E) (v : Fin m → E) :
    Nat.card (criticalFibre E⸨X⸩ m n
      ((X ^ m + powerSeriesRawDeformation E m n u).map
        (algebraMap (PowerSeries E) E⸨X⸩))
      ((X ^ n + powerSeriesReciprocalDeformation E m n v).map
        (algebraMap (PowerSeries E) E⸨X⸩))) =
      criticalHorizonMultiplicity m n := by
  rw [← Nat.card_congr (powerSeriesCriticalFibreLaurentEquiv E hm hn u v)]
  exact nat_card_powerSeriesCriticalFibre E hm hn u v

end GaloisForLFunctions.HTGeometry
