import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianOrbitPrincipalDivisors
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricPrincipalDivisorRigidity

/-!
# Degree-zero Hom spaces on the geometric Hermitian curve

Kazhdan's one-fiber rigidity lemma (arXiv:2606.23240, Lemma 2.1) applies
to sums of equal-degree lines. Here the orbit tangent products supply a
direct proof for the actual divisors of the Hermitian function field.
A nonzero section between degree-normalized lines is nowhere vanishing,
and any two such sections differ by a geometric constant.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "H" => HermitianGeometricField p s
local notation "E" => HermitianGeometricConstants p s
local notation "Pts" => HermitianGeometricPoint p s
local notation "Div" => HermitianGeometricPlaceDivisor p s
local notation "D₀" => hermitianGeometricDegreeZeroPart p s
local notation "divH" => hermitianGeometricPrincipalDivisorHom p s

/-- Every degree-normalized signed divisor class is killed by a positive integer prime to p. -/
theorem hermitianDegreeZeroPart_primeToChar_principal (D : Pts →₀ ℤ) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ ∃ u : Additive Hˣ, divH u = n • D₀ D := by
  let d := hermitianSupportPeriod p s D
  have hd : d ≠ 0 := (hermitianSupportPeriod_pos p s D).ne'
  have h2d : 2 * d ≠ 0 := mul_ne_zero (by omega) hd
  have hQ : 1 < Q := Nat.one_lt_pow (Nat.succ_ne_zero _) (Fact.out : p.Prime).one_lt
  have hN : 1 < Q ^ (2*d) := Nat.one_lt_pow h2d hQ
  have hp : p ∣ Q ^ (2*d) := dvd_pow (dvd_pow dvd_rfl (Nat.succ_ne_zero s)) h2d
  refine ⟨Q ^ (2*d) - 1, Nat.sub_pos_of_lt hN, ?_, -hermitianOrbitTangent p s D (2*d), ?_⟩
  · exact (Nat.coprime_self_sub_left hN.le).2 (Nat.coprime_one_left _)
      |>.of_dvd_right hp
  · rw [hermitianEvenOrbit_principal, ← natCast_zsmul, Nat.cast_sub hN.le, Nat.cast_pow,
      Nat.cast_pow, Nat.cast_one]

private theorem principal_effective_zero (u : Additive Hˣ) (hu : 0 ≤ divH u) : divH u = 0 := by
  let f : H := (u.toMul : Hˣ)
  exact (hermitianGeometric_principal_eq_zero_iff_constant p s f u.toMul.ne_zero).2
    ((hermitianGeometric_effective_principal_iff_constant p s f u.toMul.ne_zero).1 hu)

/-- An effective translate of a degree-normalized divisor by a principal divisor must vanish. -/
theorem hermitianDegreeZero_effective_iff (D : Pts →₀ ℤ) (u : Additive Hˣ) :
    0 ≤ divH u + D₀ D ↔ divH u + D₀ D = 0 := by
  refine ⟨fun he => ?_, fun he => he.ge⟩
  obtain ⟨n, hn, _, v, hv⟩ := hermitianDegreeZeroPart_primeToChar_principal p s D
  have hpow : divH (n • u + v) = n • (divH u + D₀ D) := by
    rw [map_add, map_nsmul, hv, nsmul_add]
  have hp := principal_effective_zero p s (n • u + v) (hpow ▸ nsmul_nonneg he n)
  apply nsmul_right_injective hn.ne'
  simpa only [hpow, nsmul_zero] using hp

private theorem degreeZero_sub (D C : Pts →₀ ℤ) : D₀ (D-C) = D₀ D - D₀ C := by
  let ψ := Finsupp.liftAddHom (α := Pts) (fun P => zmultiplesHom Div
    (hermitianGeometricPointDifference p s P))
  exact map_sub ψ D C

/-- Ordered principal-divisor comparison between two normalized lines always gives equality. -/
theorem hermitianLineHom_effective_iff (D C : Pts →₀ ℤ) (u : Additive Hˣ) :
    D₀ D ≤ divH u + D₀ C ↔ D₀ D = divH u + D₀ C := by
  have h := hermitianDegreeZero_effective_iff p s (C-D) u
  rw [degreeZero_sub, ← add_sub_assoc, sub_nonneg, sub_eq_zero] at h
  exact h.trans eq_comm

/-- Rational sections of the line of homomorphisms between two degree-normalized divisors. -/
def hermitianLineHomSections (D C : Pts →₀ ℤ) : Set H :=
  {f | f = 0 ∨ D₀ D ≤ hermitianGeometricZeroPoleDivisor p s f + D₀ C}

/-- The divisor comparison completely determines the nonzero part of the Hom space. -/
theorem hermitianLineHomSections_eq (D C : Pts →₀ ℤ) :
    hermitianLineHomSections p s D C =
      {f | f = 0 ∨ D₀ D - D₀ C = hermitianGeometricZeroPoleDivisor p s f} := by
  ext f
  by_cases hz : f = 0
  · simp [hermitianLineHomSections, hz]
  · have h := hermitianLineHom_effective_iff p s D C (Additive.ofMul (Units.mk0 f hz))
    change (_ ≤ hermitianGeometricZeroPoleDivisor p s f + _) ↔
      (_ = hermitianGeometricZeroPoleDivisor p s f + _) at h
    simp only [hermitianLineHomSections, Set.mem_setOf_eq, hz, false_or, h, sub_eq_iff_eq_add]

/-- Distinct normalized divisor classes have zero Hom space. -/
theorem hermitianLineHomSections_trivial_iff (D C : Pts →₀ ℤ) :
    hermitianLineHomSections p s D C = {0} ↔ D₀ D - D₀ C ∉ divH.range := by
  rw [hermitianLineHomSections_eq]
  constructor
  · rintro he ⟨u, hu⟩
    have hmem : (u.toMul : H) ∈
        {f : H | f = 0 ∨ D₀ D - D₀ C = hermitianGeometricZeroPoleDivisor p s f} := Or.inr hu.symm
    rw [he] at hmem
    exact u.toMul.ne_zero hmem
  · intro hn
    ext f
    change (f = 0 ∨ _ = _) ↔ f = 0
    refine ⟨?_, Or.inl⟩
    rintro (rfl | he)
    · rfl
    · by_contra hf
      exact hn ⟨Additive.ofMul (Units.mk0 f hf), he.symm⟩

/-- Evaluation against a single nonzero section identifies the whole Hom space with its scalar line. -/
theorem hermitianLineHomSections_classification (D C : Pts →₀ ℤ) :
    hermitianLineHomSections p s D C = {0} ∨
      ∃ g : Hˣ, hermitianLineHomSections p s D C = Set.range (fun c : E => algebraMap E H c * g) := by
  by_cases h : D₀ D - D₀ C ∈ divH.range
  · obtain ⟨v, hv⟩ := h
    let g := v.toMul
    have hg : hermitianGeometricZeroPoleDivisor p s (g : H) = D₀ D - D₀ C := hv
    right
    refine ⟨g, ?_⟩
    rw [hermitianLineHomSections_eq]
    ext f
    change (f = 0 ∨ _ = _) ↔ ∃ c : E, algebraMap E H c * (g : H) = f
    by_cases hf : f = 0
    · subst f
      exact ⟨fun _ => ⟨0, by rw [map_zero, zero_mul]⟩, fun _ => Or.inl rfl⟩
    rw [or_iff_right hf, ← hg, eq_comm, hermitianGeometric_principal_eq_iff_constant_multiple
      p s f (g : H) hf g.ne_zero]
    constructor
    · rintro ⟨c, _, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_, hc.symm⟩
      rintro rfl
      exact hf (by simpa using hc.symm)
  · exact Or.inl ((hermitianLineHomSections_trivial_iff p s D C).2 h)

#print axioms hermitianDegreeZeroPart_primeToChar_principal
#print axioms hermitianDegreeZero_effective_iff
#print axioms hermitianLineHom_effective_iff
#print axioms hermitianLineHomSections_eq
#print axioms hermitianLineHomSections_trivial_iff
#print axioms hermitianLineHomSections_classification

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
