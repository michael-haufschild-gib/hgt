import GaloisForLFunctions.HTGeometry.DifferentialMatrixGroupTangentTranslation
import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealAvoidingSubmonoid
import GaloisForLFunctions.HTGeometry.CommutingDerivationFromKaehler
import GaloisForLFunctions.HTGeometry.MvPolynomialInfiniteEval

/-!
# Differential generic points of infinite represented matrix groups

An injectively represented infinite `2 × 2` matrix group has a coordinate with infinite range.
Every nonzero polynomial in that coordinate is therefore a nonzero function.  Differential prime
avoidance preserves all such polynomial values and produces a differential generic field point at
which the chosen coordinate remains transcendental.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

universe u

variable {C G : Type u} [Field C] [Differential C] [Group G]

namespace DifferentialMatrixGroupRepresentation

variable (r : DifferentialMatrixGroupRepresentation (C := C) (G := G))

local instance genericAmbientFunctionDifferential : Differential (G → C) :=
  pointwiseFunctionDifferential G

local instance genericCoordinateDifferential : Differential r.coordinateAlgebra :=
  r.coordinateAlgebraDifferential

/-- An injective infinite matrix representation has an entry coordinate with infinite range. -/
theorem exists_coordinate_infinite_range [Infinite G]
    (hinj : Function.Injective r.matrix) :
    ∃ q : Fin 2 × Fin 2, (Set.range (r.coordinate q)).Infinite := by
  by_contra hnone
  push Not at hnone
  have hfinite : ∀ q : Fin 2 × Fin 2, (Set.range (r.coordinate q)).Finite := hnone
  let R : Fin 2 × Fin 2 → Set C := fun q => Set.range (r.coordinate q)
  letI finiteR (q : Fin 2 × Fin 2) : Finite (R q) := (hfinite q).to_subtype
  let e : G → ((q : Fin 2 × Fin 2) → R q) := fun g q =>
    ⟨r.coordinate q g, ⟨g, rfl⟩⟩
  have he : Function.Injective e := by
    intro g h hgh
    apply hinj
    ext i j
    have hij := congrFun hgh (i, j)
    exact congrArg Subtype.val hij
  haveI : Finite G := Finite.of_injective e he
  exact not_finite G

/-- Infinite coordinate range excludes every nonzero polynomial relation. -/
theorem aeval_coordinate_ne_zero_of_infinite_range
    (q : Fin 2 × Fin 2) (hq : (Set.range (r.coordinate q)).Infinite)
    (p : Polynomial C) (hp : p ≠ 0) :
    Polynomial.aeval (r.coordinate q) p ≠ 0 := by
  obtain ⟨x, ⟨g, rfl⟩, hx⟩ :=
    GaloisForLFunctions.exists_mem_eval_ne_zero_of_infinite_domain p hp hq
  intro hzero
  have hg := congrFun hzero g
  apply hx
  simpa [Polynomial.aeval_def] using hg

/-- Multiplicative set of all nonzero polynomial values in one coordinate. -/
def coordinatePolynomialSubmonoid (q : Fin 2 × Fin 2) : Submonoid r.coordinateAlgebra where
  carrier := {a | ∃ p : Polynomial C, p ≠ 0 ∧
    a.1 = Polynomial.aeval (r.coordinate q) p}
  one_mem' := ⟨1, one_ne_zero, by ext g; simp⟩
  mul_mem' := by
    rintro a b ⟨p, hp, hap⟩ ⟨s, hs, hbs⟩
    refine ⟨p * s, mul_ne_zero hp hs, ?_⟩
    change a.1 * b.1 = Polynomial.aeval (r.coordinate q) (p * s)
    rw [hap, hbs, map_mul]

theorem coordinatePolynomialSubmonoid_disjoint_bot
    (q : Fin 2 × Fin 2) (hq : (Set.range (r.coordinate q)).Infinite) :
    Disjoint ((⊥ : Ideal r.coordinateAlgebra) : Set r.coordinateAlgebra)
      (r.coordinatePolynomialSubmonoid q : Set r.coordinateAlgebra) := by
  rw [Set.disjoint_left]
  intro a ha ⟨p, hp, hap⟩
  have ha0 : a = 0 := by simpa using ha
  apply r.aeval_coordinate_ne_zero_of_infinite_range q hq p hp
  rw [← hap]
  exact congrArg Subtype.val ha0

theorem coordinateAlgebra_coe_aeval
    (z : r.coordinateAlgebra) (p : Polynomial C) :
    ((Polynomial.aeval z p : r.coordinateAlgebra) : G → C) =
      Polynomial.aeval (z : G → C) p := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs =>
      rw [map_add, map_add]
      ext g
      change ((Polynomial.aeval z p : r.coordinateAlgebra) : G → C) g +
          ((Polynomial.aeval z s : r.coordinateAlgebra) : G → C) g =
        Polynomial.aeval (z : G → C) p g + Polynomial.aeval (z : G → C) s g
      rw [congrFun hp g, congrFun hs g]
  | monomial n a =>
      ext g
      simp [Polynomial.aeval_def]

/-- Evaluation commutes with any algebra map out of the coordinate algebra. -/
theorem map_coordinateAlgebra_aeval {K : Type u} [CommRing K] [Algebra C K]
    (φ : r.coordinateAlgebra →ₐ[C] K) (z : r.coordinateAlgebra) (p : Polynomial C) :
    φ (Polynomial.aeval z p) = Polynomial.aeval (φ z) p := by
  have hhom : φ.comp (Polynomial.aeval z) = Polynomial.aeval (φ z) := by
    ext
    simp
  exact DFunLike.congr_fun hhom p

theorem aeval_sub_eq_zero_of_eq {K : Type u} [CommRing K] [Algebra C K]
    (z : K) {p s : Polynomial C}
    (h : Polynomial.aeval z p = Polynomial.aeval z s) :
    Polynomial.aeval z (p - s) = 0 := by
  simpa only [map_sub] using sub_eq_zero.mpr h

/-- A coordinate jet, regarded as an element of the coordinate algebra, is the corresponding
iterated derivative of the zeroth coordinate. -/
theorem coordinateJet_element_eq_differentialJet
    (ij : Fin 2 × Fin 2) (n : ℕ) :
    let c0 : r.coordinateAlgebra :=
      ⟨r.coordinate ij, Algebra.subset_adjoin ⟨(ij, 0), by
        funext g
        exact (differentialJet_zero _).symm⟩⟩
    (⟨r.coordinateJet ij n, Algebra.subset_adjoin ⟨(ij, n), rfl⟩⟩ :
      r.coordinateAlgebra) = differentialJet n c0 := by
  dsimp only
  let c0 : r.coordinateAlgebra :=
    ⟨r.coordinate ij, Algebra.subset_adjoin ⟨(ij, 0), by
      funext g
      exact (differentialJet_zero _).symm⟩⟩
  induction n with
  | zero =>
      apply Subtype.ext
      funext g
      rfl
  | succ n ih =>
      apply Subtype.ext
      change r.coordinateJet ij (n + 1) =
        ((differentialJet (n + 1) c0 : r.coordinateAlgebra) : G → C)
      rw [← r.deriv_coordinateJet, differentialJet_succ,
        r.coordinateAlgebra_deriv_coe]
      exact congrArg Differential.deriv (congrArg Subtype.val ih)

/-- Every value of the coordinate algebra lies in the differential field generated by the four
zeroth matrix coordinates under a derivation-preserving algebra map. -/
theorem map_mem_differentialAdjoin_coordinates {K : Type u} [Field K] [Algebra C K]
    [Differential K] (φ : r.coordinateAlgebra →ₐ[C] K)
    (hφδ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a))
    (c : r.coordinateAlgebra) :
    φ c ∈ differentialAdjoin C (Set.range fun ij : Fin 2 × Fin 2 =>
      φ ⟨r.coordinate ij, Algebra.subset_adjoin ⟨(ij, 0), by
        funext g
        exact (differentialJet_zero _).symm⟩⟩) := by
  let y : Fin 2 × Fin 2 → K := fun ij =>
    φ ⟨r.coordinate ij, Algebra.subset_adjoin ⟨(ij, 0), by
      funext g
      exact (differentialJet_zero _).symm⟩⟩
  have hjet (a : r.coordinateAlgebra) (n : ℕ) :
      φ (differentialJet n a) = differentialJet n (φ a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [differentialJet_succ, differentialJet_succ, hφδ]
        exact congrArg Differential.deriv ih
  refine Algebra.adjoin_induction (p := fun f _ =>
      φ ⟨f, by assumption⟩ ∈ differentialAdjoin C (Set.range y)) ?_ ?_ ?_ ?_ c.2
  · intro f hf
    obtain ⟨ijn, rfl⟩ := hf
    let c0 : r.coordinateAlgebra :=
      ⟨r.coordinate ijn.1, Algebra.subset_adjoin ⟨(ijn.1, 0), by
        funext g
        exact (differentialJet_zero _).symm⟩⟩
    rw [r.coordinateJet_element_eq_differentialJet ijn.1 ijn.2,
      hjet c0 ijn.2]
    exact differentialJet_mem_differentialAdjoin C (Set.mem_range_self ijn.1) ijn.2
  · intro c
    change φ (algebraMap C r.coordinateAlgebra c) ∈ differentialAdjoin C (Set.range y)
    rw [φ.commutes]
    exact (differentialAdjoin C (Set.range y)).algebraMap_mem c
  · intro f g hf hg hfm hgm
    change φ (⟨f, hf⟩ + ⟨g, hg⟩) ∈ differentialAdjoin C (Set.range y)
    rw [map_add φ]
    exact (differentialAdjoin C (Set.range y)).add_mem hfm hgm
  · intro f g hf hg hfm hgm
    change φ (⟨f, hf⟩ * ⟨g, hg⟩) ∈ differentialAdjoin C (Set.range y)
    rw [map_mul φ]
    exact (differentialAdjoin C (Set.range y)).mul_mem hfm hgm

/-- An infinite coordinate survives as a transcendental element of a differential generic field
point, and the four matrix entries differentially generate that field. -/
theorem exists_transcendental_differential_genericPoint
    [Algebra ℚ C]
    (q : Fin 2 × Fin 2) (hq : (Set.range (r.coordinate q)).Infinite) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra ℚ K) (_ : Algebra C K)
      (_ : Differential K) (_ : DifferentialAlgebra C K)
      (φ : r.coordinateAlgebra →ₐ[C] K),
      (∀ a, φ (Differential.deriv a) = Differential.deriv (φ a)) ∧
      Transcendental C (φ ⟨r.coordinate q, Algebra.subset_adjoin ⟨(q, 0), by
        funext g
        exact (differentialJet_zero _).symm⟩⟩) ∧
      differentialAdjoin C (Set.range fun ij : Fin 2 × Fin 2 =>
        φ ⟨r.coordinate ij, Algebra.subset_adjoin ⟨(ij, 0), by
          funext g
          exact (differentialJet_zero _).symm⟩⟩) = ⊤ := by
  classical
  let M := r.coordinatePolynomialSubmonoid q
  have hrad : (⊥ : Ideal r.coordinateAlgebra).IsRadical := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have hpow : x ^ n = 0 := by simpa using hn
    have hx0 : x = 0 := by
      apply Subtype.ext
      funext g
      have hfun := congrArg Subtype.val hpow
      have hg := congrFun hfun g
      exact IsReduced.eq_zero (x.1 g) ⟨n, hg⟩
    simpa [hx0]
  have hδ : ∀ x ∈ (⊥ : Ideal r.coordinateAlgebra),
      Differential.deriv x ∈ (⊥ : Ideal r.coordinateAlgebra) := by
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    simp
  obtain ⟨P, hPprime, hPδ, -, hPdisj⟩ :=
    exists_isPrime_disjoint_radicalDifferential hrad hδ M
      (r.coordinatePolynomialSubmonoid_disjoint_bot q hq)
  let Q := r.coordinateAlgebra ⧸ P
  letI : Differential Q := quotientDifferential P hPδ
  letI : IsDomain Q := Ideal.Quotient.isDomain P
  letI : Algebra C Q :=
    ((Ideal.Quotient.mk P).comp (algebraMap C r.coordinateAlgebra)).toAlgebra
  let K := FractionRing Q
  letI : Field K := inferInstance
  letI : Algebra Q K := inferInstance
  letI : Algebra C K := ((algebraMap Q K).comp (algebraMap C Q)).toAlgebra
  letI : Algebra ℚ K := inferInstance
  letI : Differential K := fractionRingDifferential Q
  letI : DifferentialAlgebra C K := by
    constructor
    intro c
    calc
      Differential.deriv
          (algebraMap Q K (Ideal.Quotient.mk P (algebraMap C r.coordinateAlgebra c))) =
          algebraMap Q K
            (Differential.deriv (Ideal.Quotient.mk P
              (algebraMap C r.coordinateAlgebra c))) :=
        fractionRingDifferential_algebraMap Q _
      _ = algebraMap Q K
          (Ideal.Quotient.mk P
            (Differential.deriv (algebraMap C r.coordinateAlgebra c))) := by
        rw [quotientDifferential_deriv_mk P hPδ]
      _ = algebraMap Q K
          (Ideal.Quotient.mk P
            (algebraMap C r.coordinateAlgebra (Differential.deriv c))) := by
        rw [DifferentialAlgebra.deriv_algebraMap]
  let φ : r.coordinateAlgebra →ₐ[C] K :=
    { toRingHom := (algebraMap Q K).comp (Ideal.Quotient.mk P)
      commutes' := fun _ => rfl }
  have hφδ : ∀ a, φ (Differential.deriv a) = Differential.deriv (φ a) := by
    intro a
    change algebraMap Q K (Ideal.Quotient.mk P (Differential.deriv a)) =
      Differential.deriv (algebraMap Q K (Ideal.Quotient.mk P a))
    rw [← quotientDifferential_deriv_mk P hPδ,
      fractionRingDifferential_algebraMap]
  let z : r.coordinateAlgebra :=
    ⟨r.coordinate q, Algebra.subset_adjoin ⟨(q, 0), by
      funext g
      exact (differentialJet_zero _).symm⟩⟩
  have hztrans : Transcendental C (φ z) := by
    rw [transcendental_iff_injective]
    intro p s hps
    by_contra hpne
    have hdiff : p - s ≠ 0 := sub_ne_zero.mpr hpne
    let w : r.coordinateAlgebra := Polynomial.aeval z (p - s)
    have hwcoe : w.1 = Polynomial.aeval (r.coordinate q) (p - s) := by
      exact r.coordinateAlgebra_coe_aeval z (p - s)
    have hmemM : w ∈ M := ⟨p - s, hdiff, hwcoe⟩
    have hmapzero : φ w = 0 := by
      have hnat : φ w = Polynomial.aeval (φ z) (p - s) := by
        exact r.map_coordinateAlgebra_aeval φ z (p - s)
      exact hnat.trans (aeval_sub_eq_zero_of_eq (φ z) hps)
    have hmkzero : Ideal.Quotient.mk P w = 0 := by
      apply (IsFractionRing.injective Q K)
      change φ w = φ 0
      rw [hmapzero, map_zero]
    have hmemP : w ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.mp hmkzero
    exact Set.disjoint_left.mp hPdisj hmemP hmemM
  let y : Fin 2 × Fin 2 → K := fun ij =>
    φ ⟨r.coordinate ij, Algebra.subset_adjoin ⟨(ij, 0), by
      funext g
      exact (differentialJet_zero _).symm⟩⟩
  have hgen : differentialAdjoin C (Set.range y) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨frac, hfrac⟩ := IsLocalization.surj (nonZeroDivisors Q) x
    let num : Q := frac.1
    let den : nonZeroDivisors Q := frac.2
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective num
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective den.1
    have himage : ∀ c : r.coordinateAlgebra,
        φ c ∈ differentialAdjoin C (Set.range y) :=
      r.map_mem_differentialAdjoin_coordinates φ hφδ
    have hden : algebraMap Q K den.1 ≠ 0 := by
      intro hzero
      apply nonZeroDivisors.ne_zero den.2
      apply IsFractionRing.injective Q K
      exact hzero.trans (map_zero (algebraMap Q K)).symm
    have hnumMem : algebraMap Q K (Ideal.Quotient.mk P a) ∈
        differentialAdjoin C (Set.range y) := by
      change φ a ∈ differentialAdjoin C (Set.range y)
      exact himage a
    have hdenMem : algebraMap Q K den.1 ∈ differentialAdjoin C (Set.range y) := by
      rw [← hb]
      exact himage b
    have hxEq : x = algebraMap Q K (Ideal.Quotient.mk P a) *
        (algebraMap Q K den.1)⁻¹ := by
      rw [ha]
      apply (mul_right_cancel₀ hden)
      rw [mul_assoc, inv_mul_cancel₀ hden, mul_one]
      exact hfrac
    rw [hxEq]
    exact (differentialAdjoin C (Set.range y)).mul_mem hnumMem
      ((differentialAdjoin C (Set.range y)).inv_mem hdenMem)
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    φ, hφδ, hztrans, hgen⟩

end DifferentialMatrixGroupRepresentation

end

end GaloisForLFunctions.HTGeometry
