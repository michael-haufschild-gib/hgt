import GaloisForLFunctions.RHTower.SelbergEisensteinDecomposition

open Complex

/-!
# The constant-term count `S_N(0,0;c) = φ(|c|N)/φ(N)`

At `(m,n) = (0,0)` every phase is `1`, so `S_N(0,0;c)` counts the units modulo `K = |c|N` that are `≡ 1 (mod N)`:
the kernel of the surjection `(ℤ/K)^× → (ℤ/N)^×`, of order `φ(K)/φ(N)` (`card_ker_unitsMap`, `ksum_zero_zero`).
This is the arithmetic of the constant term of the `Γ(N)` Eisenstein series.
-/

namespace GaloisForLFunctions.RHTower.SelbergRamanujanZeroZero
open GaloisForLFunctions.RHTower.SelbergPoincareFourier GaloisForLFunctions.RHTower.SelbergKloostermanCongruence

variable (N : ℕ) [NeZero N]

/-- Units modulo `K` that are `≡ 1 (mod N)` number `φ(K)/φ(N)`. -/
theorem card_ker_unitsMap {K : ℕ} [NeZero K] (h : N ∣ K) :
    Nat.card (ZMod.unitsMap h).ker * Nat.totient N = Nat.totient K := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ZMod.unitsMap h).ker
  have e := QuotientGroup.quotientKerEquivOfSurjective _ (ZMod.unitsMap_surjective h)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient] at h1
  rw [h1, mul_comm]

/-- **The `Γ(N)` Ramanujan sum at `(0,0)`**: `S_N(0,0;c) φ(N) = φ(|c|N)` for `N | c`, `c ≠ 0`. -/
theorem ksum_zero_zero {c : ℤ} (hc : c ≠ 0) (hNc : (N : ℤ) ∣ c) :
    ksum N 0 c 0 * (Nat.totient N : ℂ) = Nat.totient (c.natAbs * N) := by
  haveI hK : NeZero (c.natAbs * N) := ⟨Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hc) (NeZero.ne N)⟩
  set K := c.natAbs * N
  have hNK : N ∣ K := Dvd.intro_left _ rfl
  classical
  have hterm : ∀ r ∈ Finset.range K, (adm N).indicator (kphase N 0 0) (c, (r : ℤ)) =
      (if IsUnit (r : ZMod K) then (if (r : ZMod N) = 1 then (1 : ℂ) else 0) else 0) := by
    intro r _
    have hk : kphase N 0 0 (c, r) = 1 := by simp [kphase, phase]
    by_cases hu : IsUnit (r : ZMod K)
    · by_cases h1 : (r : ZMod N) = 1
      · rw [Set.indicator_of_mem ((adm_iff N hNc r).mpr ⟨h1, hu⟩), hk, if_pos hu, if_pos h1]
      · rw [Set.indicator_of_notMem (fun h => h1 ((adm_iff N hNc r).mp h).1), if_pos hu, if_neg h1]
    · rw [Set.indicator_of_notMem (fun h => hu ((adm_iff N hNc r).mp h).2), if_neg hu]
  have hterm' : ∀ r ∈ Finset.range K, (adm N).indicator (kphase N 0 0) (c, (r : ℤ)) =
      (if IsUnit (r : ZMod K) then (fun a : ZMod K => if (a.cast : ZMod N) = 1 then (1 : ℂ) else 0) (r : ZMod K) else 0) := by
    intro r hr
    rw [hterm r hr]; simp only [ZMod.cast_natCast hNK]
  unfold ksum
  rw [Finset.sum_congr rfl hterm', sum_range_units K (fun a => if (a.cast : ZMod N) = 1 then (1 : ℂ) else 0)]
  have hker : ∀ x : (ZMod K)ˣ, (((x : ZMod K).cast : ZMod N) = 1 ↔ x ∈ (ZMod.unitsMap hNK).ker) := by
    intro x
    rw [MonoidHom.mem_ker, Units.ext_iff]
    simp [ZMod.unitsMap_def, ZMod.castHom_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun x : (ZMod K)ˣ => ((x : ZMod K).cast : ZMod N) = 1)).card =
      Nat.card (ZMod.unitsMap hNK).ker := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [hker x]))
  rw [hcard]
  exact_mod_cast card_ker_unitsMap N hNK

end GaloisForLFunctions.RHTower.SelbergRamanujanZeroZero
