import GaloisForLFunctions.HTGeometry.GammaDimensionZeroHorizon

/-!
# The irreversible clock on the dimension-zero Gamma horizon

The linearly receding inverse-Gamma constraint is forward invariant under `Gamma`.  In the Baire
coordinates of `GammaDimensionZeroHorizon`, the induced clock is

`tau(omega)(k) = omega(k + 1) + 1`.

Thus `Gamma` deletes one inverse-sheet label and records the elapsed depth in every surviving
label.  This is an exact consequence of the static inverse-history constraint, not an assumed
flow.  Its age filtration is strictly decreasing and has empty infinite-age core; consequently
the constrained horizon has no periodic Gamma histories.  All statements are for the actual
Euler Gamma function.
-/

namespace GaloisForLFunctions

open Complex Filter Function Set Topology

noncomputable section

/-- The clock induced on Baire histories by the linearly receding Gamma constraint. -/
def gammaHorizonClock (omega : Nat -> Nat) : Nat -> Nat :=
  fun k => omega (k + 1) + 1

@[simp]
theorem gammaHorizonClock_apply (omega : Nat -> Nat) (k : Nat) :
    gammaHorizonClock omega k = omega (k + 1) + 1 := rfl

/-- Finite inverse words agree whenever their actual pole labels agree. -/
theorem gammaCodePrefix_eq_of_labels
    {N M omega nu : Nat -> Nat} {d : Nat}
    (hlabel : ∀ k, k < d -> gammaCodeLabel N omega k = gammaCodeLabel M nu k)
    (y : Complex) :
    gammaCodePrefix N omega d y = gammaCodePrefix M nu d y := by
  induction d generalizing N M omega nu with
  | zero => simp
  | succ d ih =>
      rw [gammaCodePrefix_succ, gammaCodePrefix_succ]
      congr 1
      · exact hlabel 0 (by omega)
      · apply ih
        intro k hk
        simpa [gammaCodeLabel, gammaCodeShift] using hlabel (k + 1) (by omega)

/-- The complex horizon point depends only on the sequence of actual pole labels, not on how a
label is split into a schedule and an offset word. -/
theorem gammaBaireCode_eq_of_labels
    {N M omega nu : Nat -> Nat}
    (hlabel : ∀ k, gammaCodeLabel N omega k = gammaCodeLabel M nu k) :
    gammaBaireCode N omega = gammaBaireCode M nu := by
  exact congrArg (fun u : Nat -> Complex => limUnder Filter.atTop u) (by
    funext d
    exact gammaCodePrefix_eq_of_labels (fun k _hk => hlabel k) gammaCodeBase)

theorem gammaThinSchedule_clock_label (omega : Nat -> Nat) (k : Nat) :
    gammaCodeLabel gammaThinSchedule (gammaHorizonClock omega) k =
      gammaCodeLabel (gammaCodeShift gammaThinSchedule) (gammaCodeShift omega) k := by
  simp [gammaCodeLabel, gammaThinSchedule, gammaHorizonClock, gammaCodeShift]
  omega

/-- **Exact emergent-clock law.**  On the dimension-zero horizon, actual Euler Gamma is the
delete-and-age clock `omega |-> (omega(k+1)+1)_k`. -/
theorem Gamma_gammaConstrainedHorizon_code (omega : Nat -> Nat) :
    Complex.Gamma (gammaBaireCode gammaThinSchedule omega) =
      gammaBaireCode gammaThinSchedule (gammaHorizonClock omega) := by
  calc
    Complex.Gamma (gammaBaireCode gammaThinSchedule omega) =
        gammaBaireCode (gammaCodeShift gammaThinSchedule) (gammaCodeShift omega) :=
      Gamma_gammaBaireCode gammaThinSchedule_late
    _ = gammaBaireCode gammaThinSchedule (gammaHorizonClock omega) :=
      (gammaBaireCode_eq_of_labels (gammaThinSchedule_clock_label omega)).symm

/-- The constrained horizon is forward invariant under the actual Gamma function. -/
theorem Gamma_mapsTo_gammaConstrainedHorizon :
    MapsTo Complex.Gamma gammaConstrainedHorizon gammaConstrainedHorizon := by
  rintro _ ⟨omega, rfl⟩
  exact ⟨gammaHorizonClock omega, (Gamma_gammaConstrainedHorizon_code omega).symm⟩

/-- The actual Gamma self-map of the constrained horizon. -/
def gammaConstrainedHorizonMap : gammaConstrainedHorizon -> gammaConstrainedHorizon :=
  fun z => ⟨Complex.Gamma z, Gamma_mapsTo_gammaConstrainedHorizon z.2⟩

/-- The Baire homeomorphism exactly intertwines the emergent clock with restricted Gamma. -/
theorem gammaConstrainedHorizonHomeomorph_intertwines (omega : Nat -> Nat) :
    gammaConstrainedHorizonHomeomorph (gammaHorizonClock omega) =
      gammaConstrainedHorizonMap (gammaConstrainedHorizonHomeomorph omega) := by
  apply Subtype.ext
  exact (Gamma_gammaConstrainedHorizon_code omega).symm

@[simp]
theorem gammaHorizonClock_iterate_apply (omega : Nat -> Nat) (d k : Nat) :
    (gammaHorizonClock^[d]) omega k = omega (k + d) + d := by
  induction d generalizing k with
  | zero => simp
  | succ d ih =>
      rw [Function.iterate_succ_apply']
      simp only [gammaHorizonClock_apply, ih]
      rw [show k + 1 + d = k + (d + 1) by omega]
      omega

/-- Every finite Gamma iterate reads the tail and adds the elapsed age to all surviving labels. -/
theorem Gamma_iterate_gammaConstrainedHorizon_code (omega : Nat -> Nat) (d : Nat) :
    (Complex.Gamma^[d]) (gammaBaireCode gammaThinSchedule omega) =
      gammaBaireCode gammaThinSchedule ((gammaHorizonClock^[d]) omega) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact Gamma_gammaConstrainedHorizon_code _

/-- A history has age at least `d` exactly when every one of its clock coordinates is at least
`d`. -/
theorem mem_range_gammaHorizonClock_iterate_iff (eta : Nat -> Nat) (d : Nat) :
    eta ∈ Set.range (gammaHorizonClock^[d]) ↔ ∀ k, d <= eta k := by
  constructor
  · rintro ⟨omega, rfl⟩ k
    rw [gammaHorizonClock_iterate_apply]
    omega
  · intro h
    let omega : Nat -> Nat := fun j => if d <= j then eta (j - d) - d else 0
    refine ⟨omega, funext fun k => ?_⟩
    rw [gammaHorizonClock_iterate_apply]
    simp only [omega]
    rw [if_pos (by omega : d <= k + d), Nat.add_sub_cancel_right,
      Nat.sub_add_cancel (h k)]

/-- The age filtration is nested. -/
theorem range_gammaHorizonClock_iterate_succ_subset (d : Nat) :
    Set.range (gammaHorizonClock^[d + 1]) ⊆ Set.range (gammaHorizonClock^[d]) := by
  intro eta heta
  rw [mem_range_gammaHorizonClock_iterate_iff] at heta ⊢
  exact fun k => Nat.le_of_succ_le (heta k)

/-- Every age layer is genuinely smaller than the preceding one. -/
theorem exists_mem_range_gammaHorizonClock_iterate_not_succ (d : Nat) :
    exists eta : Nat -> Nat,
      eta ∈ Set.range (gammaHorizonClock^[d]) ∧
        eta ∉ Set.range (gammaHorizonClock^[d + 1]) := by
  refine ⟨fun _ => d, ?_, ?_⟩
  · rw [mem_range_gammaHorizonClock_iterate_iff]
    simp
  · rw [mem_range_gammaHorizonClock_iterate_iff]
    simp

/-- There is no Baire history of infinite age. -/
theorem iInter_range_gammaHorizonClock_iterate_eq_empty :
    (⋂ d : Nat, Set.range (gammaHorizonClock^[d])) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro eta heta
  have hold := Set.mem_iInter.mp heta (eta 0 + 1)
  rw [mem_range_gammaHorizonClock_iterate_iff] at hold
  have := hold 0
  omega

/-- The delete-and-age clock has no positive-period histories. -/
theorem gammaHorizonClock_iterate_ne_self
    (omega : Nat -> Nat) {d : Nat} (hd : 0 < d) :
    (gammaHorizonClock^[d]) omega ≠ omega := by
  intro hfix
  have hstep : ∀ k, omega (k + d) + d = omega k := by
    intro k
    have hk := congrFun hfix k
    simpa only [gammaHorizonClock_iterate_apply] using hk
  have hmul : ∀ n, omega (n * d) + n * d = omega 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep (n * d)
        rw [Nat.succ_mul]
        omega
  have hlarge : omega 0 + 1 <= (omega 0 + 1) * d := by
    have := Nat.mul_le_mul_left (omega 0 + 1) hd
    simpa using this
  have hlast := hmul (omega 0 + 1)
  omega

/-- Consequently, the actual Gamma function has no periodic point on the constrained horizon. -/
theorem Gamma_iterate_ne_self_on_gammaConstrainedHorizon
    {z : Complex} (hz : z ∈ gammaConstrainedHorizon) {d : Nat} (hd : 0 < d) :
    (Complex.Gamma^[d]) z ≠ z := by
  rintro hperiod
  obtain ⟨omega, rfl⟩ := hz
  rw [Gamma_iterate_gammaConstrainedHorizon_code] at hperiod
  exact gammaHorizonClock_iterate_ne_self omega hd
    (gammaBaireCode_injective gammaThinSchedule_late hperiod)

/-- The `d`-fold forward image of the horizon is exactly the complex realization of the symbolic
age-`d` layer. -/
theorem Gamma_iterate_image_gammaConstrainedHorizon (d : Nat) :
    (Complex.Gamma^[d]) '' gammaConstrainedHorizon =
      Set.range (fun omega =>
        gammaBaireCode gammaThinSchedule ((gammaHorizonClock^[d]) omega)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨omega, rfl⟩, rfl⟩
    exact ⟨omega, (Gamma_iterate_gammaConstrainedHorizon_code omega d).symm⟩
  · rintro ⟨omega, rfl⟩
    exact ⟨gammaBaireCode gammaThinSchedule omega, ⟨omega, rfl⟩,
      Gamma_iterate_gammaConstrainedHorizon_code omega d⟩

/-- **Empty eternal core.**  The nested forward images of the zero-dimensional Gamma horizon
have empty intersection.  The horizon supports arbitrarily old histories, but no history is
compatible with an infinite past inside the same constraint. -/
theorem iInter_Gamma_iterate_image_gammaConstrainedHorizon_eq_empty :
    (⋂ d : Nat, (Complex.Gamma^[d]) '' gammaConstrainedHorizon) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro z hz
  have hz0 := Set.mem_iInter.mp hz 0
  rw [Gamma_iterate_image_gammaConstrainedHorizon] at hz0
  obtain ⟨eta, heta⟩ := hz0
  have hall : eta ∈ ⋂ d : Nat, Set.range (gammaHorizonClock^[d]) := by
    rw [Set.mem_iInter]
    intro d
    have hzd := Set.mem_iInter.mp hz d
    rw [Gamma_iterate_image_gammaConstrainedHorizon] at hzd
    obtain ⟨omega, homega⟩ := hzd
    refine ⟨omega, ?_⟩
    apply gammaBaireCode_injective gammaThinSchedule_late
    exact homega.trans heta.symm
  rw [iInter_range_gammaHorizonClock_iterate_eq_empty] at hall
  exact hall

/-- The exact physical theorem package: a Baire-complete, Hausdorff-dimension-zero Gamma horizon
with an emergent irreversible clock, no periodic histories, and no eternal core. -/
theorem gamma_dimensionZero_irreversibleClockHorizon :
    dimH gammaConstrainedHorizon = 0 ∧
      MapsTo Complex.Gamma gammaConstrainedHorizon gammaConstrainedHorizon ∧
      (∀ z ∈ gammaConstrainedHorizon, ∀ d, 0 < d -> (Complex.Gamma^[d]) z ≠ z) ∧
      (⋂ d : Nat, (Complex.Gamma^[d]) '' gammaConstrainedHorizon) = ∅ := by
  exact ⟨dimH_gammaConstrainedHorizon, Gamma_mapsTo_gammaConstrainedHorizon,
    fun _z hz _d hd => Gamma_iterate_ne_self_on_gammaConstrainedHorizon hz hd,
    iInter_Gamma_iterate_image_gammaConstrainedHorizon_eq_empty⟩

end

end GaloisForLFunctions
