/-
# Apex independence: nontrivial ladder charges lie outside every torsion reading of prime flux

The weld obstruction and the deck/ladder charge are two faces of one connecting-map calculus
(`WeldChargeConnecting`): every index `idx` is realized as `δ_n` of *some* weld class.  Separately,
the prime-flux lattice in real weld cohomology is killed by every torsion-valued charge
(`WeldChargeFaithfulness.prime_flux_charge_collapse`).

This module composes the two faces into a single independence theorem:

* every torsion reading of every prime-flux class is `0`;
* a nontrivial ladder/deck charge (`wCharge n idx ≠ 0`) is therefore unequal to every such reading;
* nontrivial charges remain realizable by integer symplectic weld classes — so the charge calculus is
  nonempty, but its nontrivial values cannot come from prime flux.

Applied to `ξ`: if `xiDeckCharge k ρ ≠ 1` (equivalently `2^k ∤ ord_ρ ξ`), the additive ladder charge at
`ρ` is outside every torsion image of the prime-flux lattice.  No off-line zero of `ξ` is assumed: the
statement is a constraint on *any* index whose charge is nontrivial, with `ξ`'s order as one source of
indices.

§§1–5 below are the *torsion* form (charge values): packaging of the collapse already in
`WeldChargeFaithfulness`.  That form is **not** dual-gate new knowledge.

§§6–8 are the *strong* form: a **specific** weld class in real `H²` — the ladder conversion class
`ladderWeldClass idx = weldClassHom (idx : ℝ)` — whose commuting-pair connecting value is the
integer index `idx`, and which lies **outside the image of `primeFluxHom` in `H²` itself** whenever
`idx ≠ 0`.  The independence uses injectivity of `weldClassHom` and the banked `{1} ∪ {log p}`
`ℤ`-independence (`primeLog_indep_mod_one`, transcendence of `e`).  This is class-level (not merely
post-torsion) independence of a named ladder object from prime flux.

Scope honesty: the strong form is still a composition of banked facts under a new name; it is
categorically stronger than torsion collapse, and it supplies the specific class asked for, but it does
**not** claim a new distributional no-go or an identification of this class with a geometric monodromy
class constructed from `ξ` beyond the conversion-constant dictionary `idx ↦ ord_ρ`.
-/
import GaloisForLFunctions.RHTower.WeldChargeFaithfulness
import GaloisForLFunctions.RHTower.WeldChargeConnecting
import GaloisForLFunctions.HTGeometry.WeldCircleFaithfulness
import GaloisForLFunctions.RHTower.XiDeckCharge

open scoped BigOperators

namespace GaloisForLFunctions
namespace RHTower

/-! ### §1 Prime-flux image under torsion charges is `{0}` -/

/-- **Prime-flux charge image is zero.**  Every `ZMod n`-valued charge on real weld cohomology sends
every prime-flux class to `0`.  Repackages `prime_flux_charge_collapse` through `primeFluxHom`. -/
theorem primeFluxHom_charge_eq_zero {n : ℕ} [NeZero n]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
    (c : Nat.Primes →₀ ℤ) :
    φ (primeFluxHom c) = 0 := by
  rw [primeFluxHom_apply]
  exact prime_flux_charge_collapse φ c

/-- **The charge image of the prime-flux lattice is the singleton `{0}`.** -/
theorem primeFlux_charge_image_eq
    {n : ℕ} [NeZero n]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n) :
    (Set.range fun c : Nat.Primes →₀ ℤ => φ (primeFluxHom c)) = {0} := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact primeFluxHom_charge_eq_zero φ c
  · rintro rfl
    exact ⟨0, by simp [map_zero]⟩

/-! ### §2 Nontrivial ladder charges miss the prime-flux charge image -/

/-- **Apex independence (additive).**  A nontrivial deck/ladder charge cannot equal any torsion
reading of any prime-flux class: the left side is nonzero, the right side is always `0`. -/
theorem nontrivial_wCharge_ne_primeFlux_charge {n : ℕ} [NeZero n]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
    {idx : ℤ} (hne : _root_.RHTower.wCharge n idx ≠ 0)
    (c : Nat.Primes →₀ ℤ) :
    φ (primeFluxHom c) ≠ _root_.RHTower.wCharge n idx := by
  intro h
  exact hne (h ▸ primeFluxHom_charge_eq_zero φ c)

/-- **Apex independence (membership form).**  No nontrivial charge lies in the torsion image of the
prime-flux lattice. -/
theorem nontrivial_wCharge_notMem_primeFlux_charge_image {n : ℕ} [NeZero n]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
    {idx : ℤ} (hne : _root_.RHTower.wCharge n idx ≠ 0) :
    _root_.RHTower.wCharge n idx ∉
      (Set.range fun c : Nat.Primes →₀ ℤ => φ (primeFluxHom c)) := by
  rintro ⟨c, hc⟩
  exact nontrivial_wCharge_ne_primeFlux_charge φ hne c hc

/-! ### §3 Nontrivial charges are still realized — just not by prime flux -/

/-- **Realization outside prime flux (value level).**  Every nontrivial deck charge is the connecting
map value of an explicit integer symplectic weld class, and that value is unequal to every torsion
reading of every prime-flux class.  The charge calculus is nonempty; its nontrivial values require
weld classes outside the prime-flux lattice's torsion image. -/
theorem exists_weldClass_realizing_nontrivial_outside_primeFlux {n : ℕ} [NeZero n]
    {idx : ℤ} (hne : _root_.RHTower.wCharge n idx ≠ 0) :
    ∃ (T : TwoCoboundaryAnnihilator (Multiplicative (ℤ × ℤ)) ℤ)
      (omega : twoCocycles (G := Multiplicative (ℤ × ℤ)) (A := ℤ)),
      chargeConnectingHom T n (obstructionClass omega) = _root_.RHTower.wCharge n idx ∧
        ∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
          (c : Nat.Primes →₀ ℤ),
          chargeConnectingHom T n (obstructionClass omega) ≠ φ (primeFluxHom c) := by
  obtain ⟨T, omega, hT⟩ := exists_weldClass_chargeConnectingHom_eq n idx
  refine ⟨T, omega, hT, ?_⟩
  intro φ c
  rw [hT]
  exact (nontrivial_wCharge_ne_primeFlux_charge φ hne c).symm

/-! ### §4 Capstone packaging -/

/-- **Apex independence capstone.**  For every modulus `n ≥ 1` and every nontrivial index charge:
(1) the torsion image of prime flux is `{0}`; (2) the charge misses that image; (3) the charge is
nonetheless realized by some integer weld class under the connecting map. -/
theorem apex_independence {n : ℕ} [NeZero n] {idx : ℤ}
    (hne : _root_.RHTower.wCharge n idx ≠ 0) :
    (∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
      (c : Nat.Primes →₀ ℤ), φ (primeFluxHom c) = 0) ∧
    (∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
      (c : Nat.Primes →₀ ℤ),
        φ (primeFluxHom c) ≠ _root_.RHTower.wCharge n idx) ∧
    (∃ (T : TwoCoboundaryAnnihilator (Multiplicative (ℤ × ℤ)) ℤ)
      (omega : twoCocycles (G := Multiplicative (ℤ × ℤ)) (A := ℤ)),
        chargeConnectingHom T n (obstructionClass omega) = _root_.RHTower.wCharge n idx) :=
  ⟨fun φ c => primeFluxHom_charge_eq_zero φ c,
    fun φ c => nontrivial_wCharge_ne_primeFlux_charge φ hne c,
    by
      obtain ⟨T, omega, hT, _⟩ := exists_weldClass_realizing_nontrivial_outside_primeFlux hne
      exact ⟨T, omega, hT⟩⟩

/-! ### §5 Instance: vanishing orders and the ξ ladder charge -/

/-- Additive charge of a vanishing order is zero iff the modulus divides the order. -/
theorem wCharge_order_eq_zero_iff {n : ℕ} [NeZero n] (m : ℕ) :
    _root_.RHTower.wCharge n (m : ℤ) = 0 ↔ (n : ℤ) ∣ (m : ℤ) :=
  _root_.RHTower.wCharge_eq_zero_iff (m : ℤ)

/-- Nontriviality of the additive charge of a natural order. -/
theorem wCharge_order_ne_zero_of_not_dvd {n : ℕ} [NeZero n] {m : ℕ}
    (h : ¬ n ∣ m) :
    _root_.RHTower.wCharge n (m : ℤ) ≠ 0 := by
  intro hz
  exact h (Int.natCast_dvd_natCast.mp ((wCharge_order_eq_zero_iff m).mp hz))

/-- **ξ ladder charge, additive form.**  The additive modulus-`2^k` charge of `ord_ρ ξ` vanishes iff
the multiplicative `xiDeckCharge` is trivial. -/
theorem xi_wCharge_eq_zero_iff_xiDeckCharge_eq_one (k : ℕ) (ρ : ℂ) :
    _root_.RHTower.wCharge (2 ^ k) ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ) = 0 ↔
      _root_.RHTower.xiDeckCharge k ρ = 1 := by
  haveI : NeZero (2 ^ k) := neZero_two_pow k
  rw [wCharge_order_eq_zero_iff, Int.natCast_dvd_natCast,
    _root_.RHTower.xiDeckCharge_eq_one_iff_toNat_dvd]

/-- **Apex independence for a nontrivial ξ ladder charge.**  If the level-`k` deck charge of `ξ` at
`ρ` is nontrivial, then the corresponding additive ladder charge lies outside every torsion image of
the prime-flux lattice. -/
theorem xi_nontrivial_ladder_charge_ne_primeFlux_charge (k : ℕ) (ρ : ℂ)
    (hne : _root_.RHTower.xiDeckCharge k ρ ≠ 1)
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod (2 ^ k))
    (c : Nat.Primes →₀ ℤ) :
    φ (primeFluxHom c) ≠
      _root_.RHTower.wCharge (2 ^ k) ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ) := by
  haveI : NeZero (2 ^ k) := neZero_two_pow k
  have hne' :
      _root_.RHTower.wCharge (2 ^ k) ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ) ≠ 0 := by
    intro hz
    exact hne ((xi_wCharge_eq_zero_iff_xiDeckCharge_eq_one k ρ).mp hz)
  exact nontrivial_wCharge_ne_primeFlux_charge φ hne' c

/-- **Apex independence for `ξ` under failure of a ladder rung at one point.**  If `2^k` does not
divide `ord_ρ ξ`, the additive ladder charge at `ρ` is outside every torsion reading of prime flux. -/
theorem xi_order_not_dvd_ladder_charge_ne_primeFlux (k : ℕ) (ρ : ℂ)
    (hord : ¬ 2 ^ k ∣ (analyticOrderAt _root_.RHTower.xi ρ).toNat)
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod (2 ^ k))
    (c : Nat.Primes →₀ ℤ) :
    φ (primeFluxHom c) ≠
      _root_.RHTower.wCharge (2 ^ k) ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ) := by
  haveI : NeZero (2 ^ k) := neZero_two_pow k
  exact nontrivial_wCharge_ne_primeFlux_charge φ
    (wCharge_order_ne_zero_of_not_dvd hord) c

/-- **Capstone on `ξ`.**  A nontrivial ξ ladder charge is realized by some integer weld class and is
unequal to every prime-flux torsion reading — the two apices are independent at the charge level. -/
theorem xi_apex_independence (k : ℕ) (ρ : ℂ)
    (hne : _root_.RHTower.xiDeckCharge k ρ ≠ 1) :
    let idx : ℤ := (analyticOrderAt _root_.RHTower.xi ρ).toNat
    let n : ℕ := 2 ^ k
    (∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
      (c : Nat.Primes →₀ ℤ), φ (primeFluxHom c) = 0) ∧
    (∀ (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
      (c : Nat.Primes →₀ ℤ),
        φ (primeFluxHom c) ≠ _root_.RHTower.wCharge n idx) ∧
    (∃ (T : TwoCoboundaryAnnihilator (Multiplicative (ℤ × ℤ)) ℤ)
      (omega : twoCocycles (G := Multiplicative (ℤ × ℤ)) (A := ℤ)),
        chargeConnectingHom T n (obstructionClass omega) = _root_.RHTower.wCharge n idx) := by
  haveI : NeZero (2 ^ k) := neZero_two_pow k
  have hne' :
      _root_.RHTower.wCharge (2 ^ k) ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ) ≠ 0 := by
    intro hz
    exact hne ((xi_wCharge_eq_zero_iff_xiDeckCharge_eq_one k ρ).mp hz)
  exact apex_independence hne'

/-! ### §6 The ladder conversion class — a specific object in real `H²` -/

/-- **The ladder weld class.**  The weld obstruction class whose conversion constant is the integer
index `idx` (the vanishing-order / ladder datum).  Under the weld-class embedding
`weldClassHom : ℝ ↪ H²`, this is the line point `idx · [weld_1]`. -/
def ladderWeldClass (idx : ℤ) : secondConstraintCohomology (G := WeldGroup) (A := ℝ) :=
  weldClassHom (idx : ℝ)

@[simp] theorem ladderWeldClass_zero : ladderWeldClass 0 = 0 := by
  simp [ladderWeldClass]

theorem ladderWeldClass_eq_zsmul (idx : ℤ) :
    ladderWeldClass idx = idx • weldClassHom (1 : ℝ) := by
  rw [ladderWeldClass, ← map_zsmul, zsmul_one]

/-- **Connecting value is the index.**  The commuting-pair connecting map on the ladder class returns
the conversion constant `idx` — the same integer the deck charge reads. -/
theorem connectingHom_ladderWeldClass (idx : ℤ) :
    connectingHom (commutingPairAnnihilator (G := WeldGroup) (A := ℝ)
        weldGroup_smul_trivial weldGen_comm)
      (ladderWeldClass idx) = (idx : ℝ) := by
  dsimp [ladderWeldClass, weldClassHom_apply]
  -- `weldClassHom θ = obstructionClass (cocycleOf (weldCocycle θ) _)`
  change connectingHom _ (obstructionClass _) = _
  rw [connectingHom_commutingPair weldGroup_smul_trivial weldGen_comm]
  -- value of the cocycle on the generator pair is the antisymmetry `θ`
  simpa [cocycleOf] using weldCocycle_antisymm (idx : ℝ)

/-- Integer symplectic realization of the same index as a deck charge (reused for the dual face). -/
theorem chargeConnectingHom_eq_wCharge_of_idx (n : ℕ) (idx : ℤ) :
    ∃ (T : TwoCoboundaryAnnihilator (Multiplicative (ℤ × ℤ)) ℤ)
      (omega : twoCocycles (G := Multiplicative (ℤ × ℤ)) (A := ℤ)),
      chargeConnectingHom T n (obstructionClass omega) = _root_.RHTower.wCharge n idx :=
  exists_weldClass_chargeConnectingHom_eq n idx

/-! ### §7 Strong independence: outside `primeFluxHom` in `H²` -/

/-- **Integer conversion constants are prime-log free.**  If an integer equals a finite prime-log
combination, both sides vanish — `primeLog_indep_mod_one`. -/
theorem int_eq_primeLogHom_iff (idx : ℤ) (c : Nat.Primes →₀ ℤ) :
    (idx : ℝ) = primeLogHom c ↔ idx = 0 ∧ c = 0 := by
  constructor
  · intro h
    have := primeLog_indep_mod_one c idx h.symm
    exact ⟨this.1, this.2⟩
  · rintro ⟨rfl, rfl⟩
    simp [map_zero]

/-- **Strong apex independence.**  For `idx ≠ 0`, the ladder weld class is **not** a prime-flux class:
it lies outside the image of `primeFluxHom` inside real `H²`.  This is cohomological independence, not
merely equality of torsion charges.  Proof: `weldClassHom` is injective, so membership in the prime-flux
image would force `idx = Σ n_p log p`, contradicting `{1} ∪ {log p}` independence. -/
theorem ladderWeldClass_notMem_primeFlux_image {idx : ℤ} (hne : idx ≠ 0) :
    ladderWeldClass idx ∉ Set.range primeFluxHom := by
  rintro ⟨c, hc⟩
  -- `hc : primeFluxHom c = ladderWeldClass idx`
  have hθ : (idx : ℝ) = primeLogHom c := by
    have : weldClassHom (idx : ℝ) = weldClassHom (primeLogHom c) := by
      calc weldClassHom (idx : ℝ) = ladderWeldClass idx := rfl
        _ = primeFluxHom c := hc.symm
        _ = c.sum fun p z => z • weldClassHom (Real.log (p : ℕ)) := primeFluxHom_apply c
        _ = weldClassHom (c.sum fun p z => z • Real.log (p : ℕ)) := by
            rw [map_finsuppSum]; simp_rw [map_zsmul]
        _ = weldClassHom (primeLogHom c) := by rw [primeLogHom_apply]
    exact weldClassHom_injective this
  exact hne (int_eq_primeLogHom_iff idx c |>.mp hθ).1

/-- Equivalent: equality of classes forces a trivial index. -/
theorem ladderWeldClass_eq_primeFluxHom_iff (idx : ℤ) (c : Nat.Primes →₀ ℤ) :
    ladderWeldClass idx = primeFluxHom c ↔ idx = 0 ∧ c = 0 := by
  constructor
  · intro h
    exact (int_eq_primeLogHom_iff idx c).mp (by
      have : weldClassHom (idx : ℝ) = weldClassHom (primeLogHom c) := by
        calc weldClassHom (idx : ℝ) = ladderWeldClass idx := rfl
          _ = primeFluxHom c := h
          _ = c.sum fun p z => z • weldClassHom (Real.log (p : ℕ)) := primeFluxHom_apply c
          _ = weldClassHom (c.sum fun p z => z • Real.log (p : ℕ)) := by
              rw [map_finsuppSum]; simp_rw [map_zsmul]
          _ = weldClassHom (primeLogHom c) := by rw [primeLogHom_apply]
      exact weldClassHom_injective this)
  · rintro ⟨rfl, rfl⟩
    simp [ladderWeldClass_zero, map_zero]

/-! ### §8 Capstone (strong) and ξ instance -/

/-- **Strong capstone.**  For every nonzero integer index:
1. `ladderWeldClass idx` is a specific class in real `H²`;
2. its commuting-pair connecting value is `idx`;
3. it lies outside the prime-flux image in `H²`;
4. its deck charge `wCharge n idx` is realized by an integer symplectic weld class. -/
theorem strong_apex_independence {idx : ℤ} (hne : idx ≠ 0) (n : ℕ) :
    connectingHom (commutingPairAnnihilator (G := WeldGroup) (A := ℝ)
        weldGroup_smul_trivial weldGen_comm) (ladderWeldClass idx) = (idx : ℝ) ∧
    ladderWeldClass idx ∉ Set.range primeFluxHom ∧
    ∃ (T : TwoCoboundaryAnnihilator (Multiplicative (ℤ × ℤ)) ℤ)
      (omega : twoCocycles (G := Multiplicative (ℤ × ℤ)) (A := ℤ)),
        chargeConnectingHom T n (obstructionClass omega) = _root_.RHTower.wCharge n idx :=
  ⟨connectingHom_ladderWeldClass idx,
    ladderWeldClass_notMem_primeFlux_image hne,
    chargeConnectingHom_eq_wCharge_of_idx n idx⟩

/-- Ladder class of a vanishing order of `ξ`. -/
noncomputable def xiLadderWeldClass (ρ : ℂ) : secondConstraintCohomology (G := WeldGroup) (A := ℝ) :=
  ladderWeldClass ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ)

/-- **Strong apex independence for a genuine zero of `ξ`.**  At any point where `ξ` vanishes to
positive finite order, the ladder weld class of that order lies outside the prime-flux image in `H²`
and connects to the order as a real conversion constant. -/
theorem xi_strong_apex_independence_of_zero {ρ : ℂ}
    (h0 : _root_.RHTower.xi ρ = 0) :
    connectingHom (commutingPairAnnihilator (G := WeldGroup) (A := ℝ)
        weldGroup_smul_trivial weldGen_comm) (xiLadderWeldClass ρ)
      = ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℝ) ∧
    xiLadderWeldClass ρ ∉ Set.range primeFluxHom := by
  have hord : analyticOrderAt _root_.RHTower.xi ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr
      ⟨_root_.RHTower.xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), h0⟩
  have htop : analyticOrderAt _root_.RHTower.xi ρ ≠ ⊤ :=
    _root_.RHTower.xi_orderAt_ne_top ρ
  have hne : ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ) ≠ 0 := by
    intro hz
    apply hord
    have hcoe : analyticOrderAt _root_.RHTower.xi ρ =
        ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℕ∞) :=
      (ENat.coe_toNat htop).symm
    rw [hcoe]
    exact_mod_cast hz
  refine ⟨?_, ?_⟩
  · simpa [xiLadderWeldClass] using connectingHom_ladderWeldClass
      ((analyticOrderAt _root_.RHTower.xi ρ).toNat : ℤ)
  · simpa [xiLadderWeldClass] using ladderWeldClass_notMem_primeFlux_image hne

end RHTower
end GaloisForLFunctions
