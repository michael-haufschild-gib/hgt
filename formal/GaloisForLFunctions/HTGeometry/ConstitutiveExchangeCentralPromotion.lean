import GaloisForLFunctions.HTGeometry.ConstitutiveQuadraticFilling

/-!
# Exchange residual: strict quotient versus central promotion

The integer Heisenberg law retains the failure of two generators to commute as a central carry.
Projection to `ℤ²` erases that carry.  Associativity is the cocycle identity, every commutator is
central, and no group-homomorphic section can reconstruct the promoted history.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped commutatorElement

/-- Strict commuting shadow of the two-generator exchange history. -/
abbrev ExchangeAbelian := Multiplicative (ℤ × ℤ)

/-- The cocycle promoting exchange failure to a central coordinate. -/
def exchangeCarry (u v : ℤ × ℤ) : ℤ := u.1 * v.2

theorem exchangeCarry_cocycle (u v w : ℤ × ℤ) :
    exchangeCarry u v + exchangeCarry (u + v) w =
      exchangeCarry v w + exchangeCarry u (v + w) := by
  simp only [exchangeCarry, Prod.fst_add, Prod.snd_add]
  ring

/-- Forget the central exchange history. -/
def heisExchangeProjection : Heis →* ExchangeAbelian where
  toFun p := (p.x, p.y)
  map_one' := rfl
  map_mul' p q := by
    change (p.x + q.x, p.y + q.y) = (p.x, p.y) + (q.x, q.y)
    rfl

theorem heisExchangeProjection_surjective : Function.Surjective heisExchangeProjection := by
  intro u
  refine ⟨⟨u.1, u.2, 0⟩, ?_⟩
  rfl

theorem heisExchangeProjection_eq_one_iff (p : Heis) :
    heisExchangeProjection p = 1 ↔ p.x = 0 ∧ p.y = 0 := by
  change (p.x, p.y) = (0, 0) ↔ _
  simp

theorem heisExchangeProjection_center (n : ℤ) :
    heisExchangeProjection (Heis.center n) = 1 := by
  rfl

theorem heisExchangeProjection_same_iff_center_difference (p q : Heis) :
    heisExchangeProjection p = heisExchangeProjection q ↔
      ∃ n : ℤ, p = Heis.center n * q := by
  constructor
  · intro hpq
    change (p.x, p.y) = (q.x, q.y) at hpq
    have hx : p.x = q.x := congrArg Prod.fst hpq
    have hy : p.y = q.y := congrArg Prod.snd hpq
    refine ⟨p.z - q.z, ?_⟩
    ext <;> simp [Heis.center, hx, hy]
  · rintro ⟨n, rfl⟩
    simp [heisExchangeProjection]

/-- First exchange generator. -/
def exchangeGenF : Heis := ⟨1, 0, 0⟩

/-- Second exchange generator. -/
def exchangeGenG : Heis := ⟨0, 1, 0⟩

/-- First basis element of the strict abelian shadow. -/
def exchangeBasisF : ExchangeAbelian := (1, 0)

/-- Second basis element of the strict abelian shadow. -/
def exchangeBasisG : ExchangeAbelian := (0, 1)

@[simp] theorem heisExchangeProjection_genF :
    heisExchangeProjection exchangeGenF = exchangeBasisF :=
  rfl

@[simp] theorem heisExchangeProjection_genG :
    heisExchangeProjection exchangeGenG = exchangeBasisG :=
  rfl

theorem exchangeGenerators_central_residual :
    exchangeGenF * exchangeGenG =
      Heis.center 1 * (exchangeGenG * exchangeGenF) := by
  ext <;> simp [exchangeGenF, exchangeGenG, Heis.center]

theorem exchangeGenerators_strict_shadow_commute :
    heisExchangeProjection exchangeGenF * heisExchangeProjection exchangeGenG =
      heisExchangeProjection exchangeGenG * heisExchangeProjection exchangeGenF := by
  exact mul_comm _ _

theorem heis_commutator_formula (p q : Heis) :
    comm p q = Heis.center (p.x * q.y - q.x * p.y) := by
  ext <;> simp [comm, Heis.center]
  ring

theorem every_heis_commutator_is_central (p q : Heis) :
    ∃ n : ℤ, comm p q = Heis.center n := by
  exact ⟨p.x * q.y - q.x * p.y, heis_commutator_formula p q⟩

theorem every_center_is_exchange_commutator (n : ℤ) :
    Heis.center n = comm exchangeGenF ⟨0, n, 0⟩ := by
  rw [heis_commutator_formula]
  ext <;> simp [exchangeGenF, Heis.center]

theorem heis_center_characterization (p : Heis) :
    (p * exchangeGenF = exchangeGenF * p ∧
      p * exchangeGenG = exchangeGenG * p) ↔
      p = Heis.center p.z := by
  constructor
  · rintro ⟨hF, hG⟩
    have hy : p.y = 0 := by
      have hz := congrArg Heis.z hF
      simp [exchangeGenF] at hz
      linarith
    have hx : p.x = 0 := by
      have hz := congrArg Heis.z hG
      simp [exchangeGenG] at hz
      linarith
    ext <;> simp [Heis.center, hx, hy]
  · intro hp
    rw [hp]
    exact ⟨Heis.center_comm _ _, Heis.center_comm _ _⟩

theorem commuting_heis_have_trivial_commutator {p q : Heis} (h : p * q = q * p) :
    comm p q = 1 := by
  simp only [comm]
  rw [h]
  group

theorem lifts_of_exchange_basis_have_fixed_commutator
    (p q : Heis)
    (hp : heisExchangeProjection p = exchangeBasisF)
    (hq : heisExchangeProjection q = exchangeBasisG) :
    comm p q = Heis.center 1 := by
  change (p.x, p.y) = (1, 0) at hp
  change (q.x, q.y) = (0, 1) at hq
  have hpx : p.x = 1 := congrArg Prod.fst hp
  have hpy : p.y = 0 := congrArg Prod.snd hp
  have hqx : q.x = 0 := congrArg Prod.fst hq
  have hqy : q.y = 1 := congrArg Prod.snd hq
  rw [heis_commutator_formula]
  ext <;> simp [Heis.center, hpx, hpy, hqx, hqy]

theorem lifts_of_exchange_basis_do_not_commute
    (p q : Heis)
    (hp : heisExchangeProjection p = exchangeBasisF)
    (hq : heisExchangeProjection q = exchangeBasisG) :
    p * q ≠ q * p := by
  intro hpq
  have hfixed := lifts_of_exchange_basis_have_fixed_commutator p q hp hq
  have htrivial := commuting_heis_have_trivial_commutator hpq
  have hz := congrArg Heis.z (hfixed.symm.trans htrivial)
  norm_num at hz

theorem no_heisExchangeProjection_group_section :
    ¬ ∃ s : ExchangeAbelian →* Heis,
      heisExchangeProjection.comp s = MonoidHom.id ExchangeAbelian := by
  rintro ⟨s, hs⟩
  let p := s exchangeBasisF
  let q := s exchangeBasisG
  have hp : heisExchangeProjection p = exchangeBasisF := by
    simpa [p] using
      congrArg (fun h : ExchangeAbelian →* ExchangeAbelian => h exchangeBasisF) hs
  have hq : heisExchangeProjection q = exchangeBasisG := by
    simpa [q] using
      congrArg (fun h : ExchangeAbelian →* ExchangeAbelian => h exchangeBasisG) hs
  apply lifts_of_exchange_basis_do_not_commute p q hp hq
  dsimp [p, q]
  rw [← map_mul, ← map_mul, mul_comm]

/-- The promoted residual is central. -/
theorem heis_center_mem_center (n : ℤ) : Heis.center n ∈ Subgroup.center Heis := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Heis.center_comm n g).symm

/-- **Central extension.**  The kernel of the strict projection is exactly the centre. -/
theorem heisExchangeProjection_ker : heisExchangeProjection.ker = Subgroup.center Heis := by
  ext p
  constructor
  · intro hp
    have hxy := (heisExchangeProjection_eq_one_iff p).mp (MonoidHom.mem_ker.mp hp)
    have hc : p = Heis.center p.z := by ext <;> simp [Heis.center, hxy.1, hxy.2]
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, p = Heis.center n := ⟨p.z, hc⟩
    exact heis_center_mem_center n
  · intro hp
    rw [Subgroup.mem_center_iff] at hp
    have hc := (heis_center_characterization p).mp
      ⟨(hp exchangeGenF).symm, (hp exchangeGenG).symm⟩
    refine MonoidHom.mem_ker.mpr ((heisExchangeProjection_eq_one_iff p).mpr ⟨?_, ?_⟩)
    · simpa [Heis.center] using congrArg Heis.x hc
    · simpa [Heis.center] using congrArg Heis.y hc

/-- **Exact commutator subgroup.**  Commutator subgroup and centre of the promotion coincide. -/
theorem commutator_heis_eq_center : commutator Heis = Subgroup.center Heis := by
  apply le_antisymm
  · rw [commutator_def]
    refine Subgroup.commutator_le.mpr ?_
    intro p _ q _
    obtain ⟨n, hn⟩ := every_heis_commutator_is_central p q
    have hcomm : ⁅p, q⁆ = Heis.center n := hn
    rw [hcomm]
    exact heis_center_mem_center n
  · intro p hp
    rw [Subgroup.mem_center_iff] at hp
    have hc := (heis_center_characterization p).mp
      ⟨(hp exchangeGenF).symm, (hp exchangeGenG).symm⟩
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, p = Heis.center n := ⟨p.z, hc⟩
    rw [commutator_def]
    have hrep : Heis.center n = ⁅exchangeGenF, (⟨0, n, 0⟩ : Heis)⁆ :=
      every_center_is_exchange_commutator n
    rw [hrep]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **The strict shadow is the quotient by the promoted central residual.** -/
noncomputable def heisStrictShadowEquiv :
    Heis ⧸ Subgroup.center Heis ≃* ExchangeAbelian :=
  (QuotientGroup.quotientMulEquivOfEq heisExchangeProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ heisExchangeProjection_surjective)

theorem constitutiveExchangeCentralPromotionMechanism_closed :
    (∀ u v w : ℤ × ℤ,
      exchangeCarry u v + exchangeCarry (u + v) w =
        exchangeCarry v w + exchangeCarry u (v + w)) ∧
    Function.Surjective heisExchangeProjection ∧
    heisExchangeProjection.ker = Subgroup.center Heis ∧
    commutator Heis = Subgroup.center Heis ∧
    exchangeGenF * exchangeGenG =
      Heis.center 1 * (exchangeGenG * exchangeGenF) ∧
    (∀ p q : Heis, comm p q = Heis.center (p.x * q.y - q.x * p.y)) ∧
    (∀ n : ℤ, ∃ p q : Heis, Heis.center n = comm p q) ∧
    (∀ p q : Heis,
      heisExchangeProjection p = exchangeBasisF →
      heisExchangeProjection q = exchangeBasisG →
      p * q ≠ q * p) ∧
    ¬ ∃ s : ExchangeAbelian →* Heis,
      heisExchangeProjection.comp s = MonoidHom.id ExchangeAbelian := by
  exact ⟨exchangeCarry_cocycle, heisExchangeProjection_surjective,
    heisExchangeProjection_ker, commutator_heis_eq_center,
    exchangeGenerators_central_residual, heis_commutator_formula,
    (fun n => ⟨exchangeGenF, ⟨0, n, 0⟩, every_center_is_exchange_commutator n⟩),
    lifts_of_exchange_basis_do_not_commute,
    no_heisExchangeProjection_group_section⟩

end GaloisForLFunctions.HTGeometry
