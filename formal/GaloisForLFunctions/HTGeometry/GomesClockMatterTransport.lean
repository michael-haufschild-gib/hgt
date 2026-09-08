import GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy

/-!
# Matter transport and charge visibility for clock holonomy

Gomes, arXiv:2404.10461v1, Section 2, describes the common origin of transport
in associated matter representations. Here the same construction is applied
to the corpus's graph-walk calibration transport: a representation commutes
with every walk product and every gauge change.

The tensor charge law of arXiv:2509.25276v7 and the reconstruction obstruction
of arXiv:2607.24901v1, Section 4.3, become exact arithmetic statements. Two
integer charges observe precisely the gcd power of relative holonomy.
Consecutive charges recover holonomy completely. No compactness is required.
-/

namespace GaloisForLFunctions.HTGeometry

variable {V A B : Type*} {G : SimpleGraph V}

/-- Associated transport is determined by one fundamental transport. -/
theorem clockWalkTransport_map [Monoid A] [Monoid B]
    (ρ : A →* B) (c : V → V → A) {u v : V} (p : G.Walk u v) :
    clockWalkTransport (fun x y => ρ (c x y)) p = ρ (clockWalkTransport c p) := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [clockWalkTransport_cons, ih, map_mul]

/-- The same local gauge field acts coherently on every matter representation. -/
theorem clockCalibrationGauge_map [Group A] [Group B]
    (ρ : A →* B) (g : V → A) (c : V → V → A) :
    clockCalibrationGauge (fun x => ρ (g x)) (fun x y => ρ (c x y)) =
      fun x y => ρ (clockCalibrationGauge g c x y) := by
  funext x y
  simp [clockCalibrationGauge]

/-- Endpoint covariance is inherited by every associated representation. -/
theorem clockMatterTransport_gauge [Group A] [Group B]
    (ρ : A →* B) (g : V → A) (c : V → V → A)
    {u v : V} (p : G.Walk u v) :
    clockWalkTransport (fun x y => ρ (clockCalibrationGauge g c x y)) p =
      (ρ (g u))⁻¹ * ρ (clockWalkTransport c p) * ρ (g v) := by
  rw [clockWalkTransport_map, clockWalkTransport_gauge]
  simp only [map_mul, map_inv]

/-- Integer tensor charge as a representation of any commutative gauge group. -/
def clockChargeRepresentation [CommGroup A] (n : ℤ) : A →* A where
  toFun a := a ^ n
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n

/-- Every charged sector sees exactly the corresponding power of transport. -/
theorem clockWalkTransport_charge [CommGroup A]
    (n : ℤ) (c : V → V → A) {u v : V} (p : G.Walk u v) :
    clockWalkTransport (fun x y => c x y ^ n) p = clockWalkTransport c p ^ n :=
  clockWalkTransport_map (clockChargeRepresentation n) c p

/-- Tensoring two charged sectors adds their charges on every open path. -/
theorem clockWalkTransport_tensor_charge [CommGroup A]
    (m n : ℤ) (c : V → V → A) {u v : V} (p : G.Walk u v) :
    clockWalkTransport (fun x y => c x y ^ (m+n)) p =
      clockWalkTransport (fun x y => c x y ^ m) p *
      clockWalkTransport (fun x y => c x y ^ n) p := by
  rw [clockWalkTransport_charge, clockWalkTransport_charge,
    clockWalkTransport_charge, zpow_add]

/-- Dualizing a charged sector reverses its transport. -/
theorem clockWalkTransport_dual_charge [CommGroup A]
    (n : ℤ) (c : V → V → A) {u v : V} (p : G.Walk u v) :
    clockWalkTransport (fun x y => c x y ^ (-n)) p =
      (clockWalkTransport (fun x y => c x y ^ n) p)⁻¹ := by
  rw [clockWalkTransport_charge, clockWalkTransport_charge, zpow_neg]

/-- Two charges lose exactly the torsion measured by their integer gcd. -/
theorem clockCharge_pair_visibility [CommGroup A] (m n : ℤ) (a b : A) :
    (a^m = b^m ∧ a^n = b^n) ↔ (a*b⁻¹) ^ Int.gcd m n = 1 := by
  rw [pow_intGCD_eq_one]
  simp only [mul_zpow, inv_zpow, mul_inv_eq_one]

/-- Exact reconstruction boundary for two charged observations of arbitrary edge fields. -/
theorem clockMatterTransport_pair_visibility [CommGroup A]
    (m n : ℤ) (c d : V → V → A) {u v : V} (p : G.Walk u v) :
    (clockWalkTransport (fun x y => c x y ^ m) p =
        clockWalkTransport (fun x y => d x y ^ m) p ∧
      clockWalkTransport (fun x y => c x y ^ n) p =
        clockWalkTransport (fun x y => d x y ^ n) p) ↔
      (clockWalkTransport c p * (clockWalkTransport d p)⁻¹) ^ Int.gcd m n = 1 := by
  simp only [clockWalkTransport_charge]
  exact clockCharge_pair_visibility m n _ _

/-- Two consecutive tensor charges recover the entire transport element. -/
theorem clockCharge_consecutive_visibility [CommGroup A] (n : ℤ) (a b : A) :
    (a^n = b^n ∧ a^(n+1) = b^(n+1)) ↔ a = b := by
  constructor
  · rintro ⟨h, hs⟩
    rw [zpow_add, zpow_add, zpow_one, zpow_one, h] at hs
    exact mul_left_cancel hs
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- No fundamental holonomy remains invisible to consecutive charged sectors. -/
theorem clockMatterTransport_consecutive_reconstruction [CommGroup A]
    (n : ℤ) (c d : V → V → A) {u v : V} (p : G.Walk u v) :
    (clockWalkTransport (fun x y => c x y ^ n) p =
        clockWalkTransport (fun x y => d x y ^ n) p ∧
      clockWalkTransport (fun x y => c x y ^ (n+1)) p =
        clockWalkTransport (fun x y => d x y ^ (n+1)) p) ↔
      clockWalkTransport c p = clockWalkTransport d p := by
  simp only [clockWalkTransport_charge]
  exact clockCharge_consecutive_visibility n _ _

/-- The fundamental transport has an explicit reconstruction from adjacent charges. -/
theorem clockMatterTransport_consecutive_formula [CommGroup A]
    (n : ℤ) (c : V → V → A) {u v : V} (p : G.Walk u v) :
    clockWalkTransport c p =
      clockWalkTransport (fun x y => c x y ^ (n+1)) p *
        (clockWalkTransport (fun x y => c x y ^ n) p)⁻¹ := by
  rw [clockWalkTransport_charge, clockWalkTransport_charge, zpow_add, zpow_one]
  group

end GaloisForLFunctions.HTGeometry
