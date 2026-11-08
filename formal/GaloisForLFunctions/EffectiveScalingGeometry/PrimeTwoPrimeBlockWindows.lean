import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockHomology

/-!
# Exact coefficient windows of arithmetic two-prime blocks

The lower branch is `R` on `[m,2m)` and `R/2R` on `[2m,3m)`.
The upper branch is `Ann_R(2)` on `[2m,3m)` and `R` on `[3m,6m)`.
Outside these windows the corresponding homology vanishes. The equivalences
retain the scalar cycle coordinate, so they describe the original block
homology through its canonical coefficient quotient.
-/

noncomputable section
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

theorem twoPrimeBlockScalar_before (m N : ℕ) (h : N < m) :
    twoPrimeBlockScalar R m N = ⊥ := by
  ext c
  constructor
  · intro hc
    exact hc h
  · intro hc _
    exact hc

theorem twoPrimeBlockScalar_after (m N : ℕ) (h : m ≤ N) :
    twoPrimeBlockScalar R m N = ⊤ := by
  ext c
  constructor
  · intro _
    trivial
  · intro _ hn
    exact False.elim (by omega)

/-- There are no upper cycles before the two-tag is born. -/
theorem twoPrimeUpperCoefficients_before (m N : ℕ) (h : N < 2*m) :
    twoPrimeUpperCoefficients R m N = ⊥ := by
  ext c
  constructor
  · intro hc
    exact hc.1 h
  · intro hc
    change c=0 at hc
    rw [hc]
    exact ⟨fun _ => rfl,fun _ => mul_zero _⟩

/-- Between the two-tag and three-tag births, cycles are precisely two-torsion. -/
theorem twoPrimeUpperCoefficients_annihilator (m N : ℕ) (h2 : 2*m ≤ N) (h3 : N < 3*m) :
    twoPrimeUpperCoefficients R m N = twoPrimeAnnihilator R := by
  ext c
  constructor
  · intro hc
    exact hc.2 h3
  · intro hc
    exact ⟨fun h => False.elim (by omega),fun _ => hc⟩

/-- After the three-tag birth, the row kernel has one arbitrary ring coefficient. -/
theorem twoPrimeUpperCoefficients_after (m N : ℕ) (h : 3*m ≤ N) :
    twoPrimeUpperCoefficients R m N = ⊤ := by
  ext c
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨fun hn => False.elim (by omega),fun hn => False.elim (by omega)⟩

/-- No upper relation exists before the top face is born. -/
theorem twoPrimeUpperRelations_before (m N : ℕ) (h : N < 6*m) :
    twoPrimeUpperRelations R m N = ⊥ := by
  ext c
  constructor
  · intro hc
    apply Subtype.ext
    exact hc h
  · intro hc
    change c=0 at hc
    rw [hc]
    exact Submodule.zero_mem _

/-- The top face kills every upper cycle. -/
theorem twoPrimeUpperRelations_after (m N : ℕ) (h : 6*m ≤ N) :
    twoPrimeUpperRelations R m N = ⊤ := by
  ext c
  constructor
  · intro _
    trivial
  · intro _ hn
    exact False.elim (by omega)

/-- Lower relations are absent before the two-tag birth. -/
theorem twoPrimeLowerRelations_before (m N : ℕ) (h : N < 2*m) :
    twoPrimeLowerRelations R m N = ⊥ := by
  ext c
  change c.val ∈ twoPrimeLowerIdeal R m N ↔ c=0
  rw [twoPrimeLowerIdeal,if_neg (by omega),if_neg (by omega)]
  constructor
  · intro hc
    exact Subtype.ext hc
  · intro hc
    rw [hc]
    exact Submodule.zero_mem _

/-- Once the three-tag appears, every bottom coefficient is a boundary. -/
theorem twoPrimeLowerRelations_after (m N : ℕ) (h : 3*m ≤ N) :
    twoPrimeLowerRelations R m N = ⊤ := by
  ext c
  change c.val ∈ twoPrimeLowerIdeal R m N ↔ True
  rw [twoPrimeLowerIdeal,if_pos h]
  exact iff_true_intro (Submodule.mem_top)

/-- A born scalar generator is canonically the coefficient ring. -/
def twoPrimeBlockScalarEquiv (m N : ℕ) (h : m ≤ N) :
    twoPrimeBlockScalar R m N ≃ₗ[R] R where
  toFun c := c.val
  invFun c := ⟨c,fun hn => False.elim (by omega)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The upper free window retains the kernel coefficient. -/
def twoPrimeUpperCoefficientsEquiv (m N : ℕ) (h : 3*m ≤ N) :
    twoPrimeUpperCoefficients R m N ≃ₗ[R] R where
  toFun c := c.val
  invFun c := ⟨c,⟨fun hn => False.elim (by omega),fun hn => False.elim (by omega)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Lower homology before the two-tag birth is one free ring coefficient. -/
def twoPrimeLowerFreeEquiv (m N : ℕ) (hm : m ≤ N) (h2 : N < 2*m) :
    TwoPrimeLowerHomology R m N ≃ₗ[R] R :=
  ((twoPrimeLowerRelations R m N).quotEquivOfEqBot (twoPrimeLowerRelations_before R m N h2)).trans
    (twoPrimeBlockScalarEquiv R m N hm)

/-- The lower middle window is the ring modulo twice the ring. -/
def twoPrimeLowerModTwoEquiv (m N : ℕ) (h2 : 2*m ≤ N) (h3 : N < 3*m) :
    TwoPrimeLowerHomology R m N ≃ₗ[R]
      R ⧸ ((2 : R) • (LinearMap.id : R →ₗ[R] R)).range :=
  Submodule.Quotient.equiv (twoPrimeLowerRelations R m N)
    ((2 : R) • (LinearMap.id : R →ₗ[R] R)).range
    (twoPrimeBlockScalarEquiv R m N (by omega)) (by
      ext c
      constructor
      · rintro ⟨a,ha,rfl⟩
        change a.val ∈ twoPrimeLowerIdeal R m N at ha
        rw [twoPrimeLowerIdeal,if_neg (by omega),if_pos h2] at ha
        exact ha
      · intro hc
        refine ⟨⟨c,fun hn => False.elim (by omega)⟩,?_,rfl⟩
        change c ∈ twoPrimeLowerIdeal R m N
        rw [twoPrimeLowerIdeal,if_neg (by omega),if_pos h2]
        exact hc)

/-- The upper middle window is exactly the annihilator of two. -/
def twoPrimeUpperAnnihilatorEquiv (m N : ℕ) (h2 : 2*m ≤ N) (h3 : N < 3*m) :
    TwoPrimeUpperHomology R m N ≃ₗ[R] twoPrimeAnnihilator R :=
  ((twoPrimeUpperRelations R m N).quotEquivOfEqBot
    (twoPrimeUpperRelations_before R m N (by omega))).trans
      (LinearEquiv.ofEq _ _ (twoPrimeUpperCoefficients_annihilator R m N h2 h3))

/-- The upper final window is one free ring coefficient. -/
def twoPrimeUpperFreeEquiv (m N : ℕ) (h3 : 3*m ≤ N) (h6 : N < 6*m) :
    TwoPrimeUpperHomology R m N ≃ₗ[R] R :=
  ((twoPrimeUpperRelations R m N).quotEquivOfEqBot (twoPrimeUpperRelations_before R m N h6)).trans
    (twoPrimeUpperCoefficientsEquiv R m N h3)

/-- The lower branch is absent before the bottom generator appears. -/
theorem twoPrimeLowerHomology_before (m N : ℕ) (h : N < m)
    (x : TwoPrimeLowerHomology R m N) : x=0 := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations R m N) x
  have hc : c=0 := Subtype.ext (c.property h)
  rw [hc,map_zero]

/-- The lower branch dies when both small-prime vertices have appeared. -/
theorem twoPrimeLowerHomology_after (m N : ℕ) (h : 3*m ≤ N)
    (x : TwoPrimeLowerHomology R m N) : x=0 := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations R m N) x
  change (Submodule.Quotient.mk c : TwoPrimeLowerHomology R m N)=0
  rw [Submodule.Quotient.mk_eq_zero,twoPrimeLowerRelations_after R m N h]
  trivial

/-- The upper branch is absent before the two-tag birth. -/
theorem twoPrimeUpperHomology_before (m N : ℕ) (h : N < 2*m)
    (x : TwoPrimeUpperHomology R m N) : x=0 := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations R m N) x
  have hc : c=0 := Subtype.ext (c.property.1 h)
  rw [hc,map_zero]

/-- The upper branch dies when the top face appears. -/
theorem twoPrimeUpperHomology_after (m N : ℕ) (h : 6*m ≤ N)
    (x : TwoPrimeUpperHomology R m N) : x=0 := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations R m N) x
  change (Submodule.Quotient.mk c : TwoPrimeUpperHomology R m N)=0
  rw [Submodule.Quotient.mk_eq_zero,twoPrimeUpperRelations_after R m N h]
  trivial

#print axioms twoPrimeLowerFreeEquiv
#print axioms twoPrimeLowerModTwoEquiv
#print axioms twoPrimeUpperAnnihilatorEquiv
#print axioms twoPrimeUpperFreeEquiv
#print axioms twoPrimeLowerHomology_before
#print axioms twoPrimeLowerHomology_after
#print axioms twoPrimeUpperHomology_before
#print axioms twoPrimeUpperHomology_after
end GaloisForLFunctions.EffectiveScalingGeometry
