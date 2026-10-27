import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheRamanujanTwinsSurviveExactlyOnPerOrderRelations
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# The Ramanujan twins carry the primes

Shift the Ramanujan modes by one step, `c_n(k + 1)`, so that the twin germ at the pole node
`x = 0` is `Σ_{k ≥ 0} r^k c_m(k+1) c_n(k+1)/(k + 1)`. Then:

* **The pole-node block is the torsion energy** (`torsionEnergy_eq_mul_twistedGerm`):
  `T_r(m, n) = r · Σ_k r^k c_m(k+1) c_n(k+1)/(k + 1)`, the Abel energy of the torsion orbits of
  AET.
* **Its limit is the orbit intersection** (`tendsto_twin_poleNode`): for `m ≠ n` the pole-node
  entry tends to `−I(m, n)`, and `I(m, mt) = φ(m)Λ(t)`.
* **The twin carries the primes** (`ramanujanTwin_carries_primes`). Every renormalized limit `A`
  of the shifted twin is nonnegative on the per-order relations, and its entries at two pole nodes
  of orders `m` and `mt` are `−φ(m)Λ(t)`.

So the survival inequality of the twin is an inequality in which von Mangoldt's function enters
through the pole-node block, against the twisted entries at the other nodes: the precise sense in
which matched renormalization of the torsion orbits constrains Weil's prime kernel.
-/

noncomputable section

open Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open ArithmeticEffectivityTheory

/-- The shifted Ramanujan mode `k ↦ c_n(k + 1)`. -/
def shiftedMode (n k : ℕ) : ℝ := ramanujanMode n (k + 1)

theorem shiftedMode_periodic {n : ℕ} (hn : 0 < n) : Function.Periodic (shiftedMode n) n :=
  fun k => by
    simp only [shiftedMode, show k + n + 1 = (k + 1) + n by ring]
    exact ramanujanMode_periodic hn (k + 1)

/-- Shifted Ramanujan modes are orthogonal over a common period. -/
theorem sum_shiftedMode_mul {m n q : ℕ} (hm : 0 < m) (hn : 0 < n) (hmq : m ∣ q) (hnq : n ∣ q) :
    ∑ k ∈ range q, shiftedMode m k * shiftedMode n k =
      if m = n then (q : ℝ) * Nat.totient n else 0 := by
  have hper : Function.Periodic (fun k => ramanujanMode m k * ramanujanMode n k) q := by
    intro k
    have h1 := (ramanujanMode_periodic hm).nat_mul (q / m)
    have h2 := (ramanujanMode_periodic hn).nat_mul (q / n)
    rw [Nat.cast_id, Nat.div_mul_cancel hmq] at h1
    rw [Nat.cast_id, Nat.div_mul_cancel hnq] at h2
    simp only [h1 k, h2 k]
  have hshift := sum_range_shift_of_periodic
    (p := fun k => ramanujanMode m k * ramanujanMode n k) hper 1
  simp only [shiftedMode]
  rw [show ∑ k ∈ range q, ramanujanMode m (k + 1) * ramanujanMode n (k + 1) =
      ∑ k ∈ range q, ramanujanMode m (1 + k) * ramanujanMode n (1 + k) from
    sum_congr rfl fun k _ => by rw [add_comm], hshift]
  exact sum_ramanujanMode_mul hm hn hmq hnq

/-- **The pole-node block is the torsion energy.** -/
theorem torsionEnergy_eq_mul_twistedGerm {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    torsionEnergy r m n = r * twistedGerm (fun k => shiftedMode m k * shiftedMode n k) r 1 := by
  have hper : Function.Periodic (fun k => shiftedMode m k * shiftedMode n k) (m * n) := by
    have h1 := (shiftedMode_periodic hm).nat_mul n
    have h2 := (shiftedMode_periodic hn).nat_mul m
    rw [Nat.cast_id, mul_comm n m] at h1
    rw [Nat.cast_id] at h2
    exact h1.mul h2
  have hmn : 0 < m * n := mul_pos hm hn
  have hB := abs_le_of_periodic hmn hper
  have hg := (summable_twistedGerm hB hr0 hr1 one_pos).hasSum.mul_left r
  -- Drop the vanishing `k = 0` term of the torsion series and shift.
  have hT := hasSum_torsionEnergy hr0 hr1 m n
  have hT1 := (hasSum_nat_add_iff' 1).mpr hT
  simp only [range_one, sum_singleton, Nat.cast_zero, div_zero, zero_mul, sub_zero] at hT1
  refine hT1.unique (hg.congr_fun fun k => ?_)
  have hre : (ramanujanSum m (k + 1) * conj (ramanujanSum n (k + 1))).re =
      shiftedMode m k * shiftedMode n k := by
    rw [ramanujanSum_eq_ofReal, ramanujanSum_eq_ofReal, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    rfl
  rw [hre]
  push_cast
  ring

/-- **The pole-node entry tends to minus the orbit intersection.** -/
theorem tendsto_twin_poleNode {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Tendsto (fun r => twistedGerm (fun k => shiftedMode m k * shiftedMode n k) r 1) (𝓝[<] 1)
      (𝓝 (-orbitIntersection m n)) := by
  have hT := (tendsto_torsionEnergy_of_ne hmn).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  have hinv : Tendsto (fun r : ℝ => r⁻¹) (𝓝[<] 1) (𝓝 1) := by
    have h := (continuousAt_inv₀ (one_ne_zero (α := ℝ))).tendsto
    rw [inv_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h := hT.mul hinv
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  rw [torsionEnergy_eq_mul_twistedGerm hr.1.le hr.2 hm hn]
  field_simp [hr.1.ne']

/-- **The twin carries the primes.** For shifted Ramanujan modes of orders `ord α` at nodes `x α`,
there is a renormalized limit `A` of the twin that is nonnegative on every per-order relation and
whose entries at two pole nodes of different orders are minus the orbit intersections. -/
theorem ramanujanTwin_carries_primes {N : ℕ} (ord : Fin N → ℕ) (hord : ∀ α, 0 < ord α)
    {x : Fin N → ℝ} (hx : ∀ α, 0 ≤ x α) :
    ∃ A : Matrix (Fin N) (Fin N) ℝ,
      (∀ α β, Tendsto (fun r => periodicGerm (fun α => shiftedMode (ord α)) x r α β -
        (-Real.log (1 - r)) * cesaroGram (fun α => shiftedMode (ord α)) (twinPeriod ord) α β)
          (𝓝[<] 1) (𝓝 (A α β))) ∧
      (∀ C : Fin N → ℝ, (∀ m : ℕ, ∑ α ∈ univ.filter (fun α => ord α = m), C α = 0) →
        0 ≤ quad A C) ∧
      (∀ α β, x α = 0 → x β = 0 → ord α ≠ ord β →
        A α β = -orbitIntersection (ord α) (ord β)) := by
  classical
  have hq : 0 < twinPeriod ord := prod_pos fun γ _ => hord γ
  have hper : ∀ α, Function.Periodic (shiftedMode (ord α)) (twinPeriod ord) := by
    intro α
    have h := (shiftedMode_periodic (hord α)).nat_mul (twinPeriod ord / ord α)
    rwa [Nat.cast_id, Nat.div_mul_cancel (dvd_twinPeriod ord α)] at h
  obtain ⟨A, hA, hpos⟩ := periodicGerm_survival (fun α => shiftedMode (ord α)) hq hper hx
  refine ⟨A, hA, fun C hC => hpos C fun k => ?_, fun α β hxα hxβ hne => ?_⟩
  · exact (ramanujanRelations_iff ord hord C).mpr hC (k + 1)
  · -- The Cesàro entry vanishes by orthogonality; the germ entry tends to `−I`.
    have hM : cesaroGram (fun α => shiftedMode (ord α)) (twinPeriod ord) α β = 0 := by
      simp only [cesaroGram, Matrix.of_apply, periodMean]
      rw [sum_shiftedMode_mul (hord α) (hord β) (dvd_twinPeriod ord α) (dvd_twinPeriod ord β),
        if_neg hne, zero_div]
    have hlim := tendsto_twin_poleNode (hord α) (hord β) hne
    refine tendsto_nhds_unique (hA α β) (hlim.congr fun r => ?_)
    simp only [periodicGerm, Matrix.of_apply, hxα, hxβ, add_zero, hM, mul_zero, sub_zero]

/-- **Von Mangoldt in the twin.** At pole nodes of orders `m` and `mt`, `t > 1`, the renormalized
twin entry is `−φ(m)Λ(t)`. -/
theorem ramanujanTwin_poleNode_vonMangoldt {N : ℕ} (ord : Fin N → ℕ) (hord : ∀ α, 0 < ord α)
    {x : Fin N → ℝ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : ∀ α β, x α = 0 → x β = 0 → ord α ≠ ord β →
      A α β = -orbitIntersection (ord α) (ord β))
    {α β : Fin N} (hxα : x α = 0) (hxβ : x β = 0) {t : ℕ} (ht : 1 < t)
    (hord' : ord β = ord α * t) :
    A α β = -((Nat.totient (ord α) : ℝ) * Λ t) := by
  have hne : ord α ≠ ord β := by
    rw [hord']
    intro h
    have h1 : ord α * 1 = ord α * t := by rw [mul_one]; exact h
    have := Nat.eq_of_mul_eq_mul_left (hord α) h1
    omega
  rw [hA α β hxα hxβ hne, hord', orbitIntersection_hecke (hord α) ht]

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
