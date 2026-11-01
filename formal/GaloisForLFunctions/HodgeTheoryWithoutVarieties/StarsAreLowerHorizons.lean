import GaloisForLFunctions.ArithmeticCouplingTheory.TheMertensPolarization
import GaloisForLFunctions.ArithmeticElectrostatics.TheWeilPrimeFormOnAtomsIsLogarithmic

/-!
# Stars of the divisibility complex are lower horizons

The divisibility complex of `[1, N]` has vertices `n` of mass `1/n` and dilation edges `(n, kn)`
of weight `λ(k)/k` for a weight `λ` (Weil's case `λ = Λ`). Its quadratic forms in packet
coordinates `F` are

* the **dilation form** `P^λ_N(F) = Σ_{kn ≤ N} (λ(k)/k) 2F(n)F(kn)/n`,
* the **dilation energy** `J^λ_N(F) = Σ_{kn ≤ N} (λ(k)/k)(F(kn) − F(n))²/n`, the graph Laplacian,
* the **degree diagonal** `Σ_n F(n)²/n (out(⌊N/n⌋) + in(n))` with out-degree
  `out(M) = Σ_{k ≤ M} λ(k)/k` and in-degree `in(n) = Σ_{k ∣ n} λ(k) = (λ ∗ 1)(n)`.

**Polarization** (`dilationForm_eq`): `P^λ = diagonal − J^λ` for every weight; for `λ = Λ` this is
ACoT's Mertens polarization.

The **star** of `d` is the set of multiples of `d`. The map `m ↦ dm` identifies the dilation graph
of `[1, ⌊N/d⌋]` with the star, every weight divided by `d`. So:

* the dilation form of a packet supported on the star is the form at horizon `⌊N/d⌋`
  (`dilationForm_starRestrict`), for every weight;
* the degree diagonal and the dilation energy each pick up the same **boundary flux**
  `flux(d, m) = in(dm) − in(m)`: the weight entering the star at `dm` from outside it
  (`degreeDiagonal_starRestrict`, `dilationEnergy_starRestrict`);
* for `λ = Λ` the flux is `log d` at every vertex because `Λ ∗ 1 = log` (`starFlux_vonMangoldt`),
  so the jump energy and the Mertens diagonal of the star are those of horizon `⌊N/d⌋` plus
  `log d` times the mass (`jumpEnergy_starRestrict`, `mertensDiagonal_starRestrict`).

In Weil's coordinates `x_n = F(n)/√n` the prime kernel depends only on ratios
(`weilPrimeKernel_mul_mul`), so `atomicWeilForm` on the star of `d` is `atomicWeilForm` at
`⌊N/d⌋` (`atomicWeilForm_starRestrict`). The renormalized prime form `(log N − γ)|x|² − P_N(x)` on
the star is the renormalized form at `⌊N/d⌋` plus `(log N − log ⌊N/d⌋)|x|²`
(`renormalizedPrimeForm_starRestrict`): the running counterterm pays exactly the boundary flux.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.ArithmeticCouplingTheory GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticEffectivityTheory

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-! ### The weighted dilation complex -/

/-- The dilation form `P^λ_N(F) = Σ_{kn ≤ N} (λ(k)/k) 2F(n)F(kn)/n`. -/
def dilationForm (lam : ℕ → ℝ) (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ p ∈ dilationPairs N, lam p.1 / p.1 * (2 * F p.2 * F (p.1 * p.2) / p.2)

/-- The dilation energy `J^λ_N(F) = Σ_{kn ≤ N} (λ(k)/k)(F(kn) − F(n))²/n`. -/
def dilationEnergy (lam : ℕ → ℝ) (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ p ∈ dilationPairs N, lam p.1 / p.1 * ((F (p.1 * p.2) - F p.2) ^ 2 / p.2)

/-- The in-degree `(λ ∗ 1)(n) = Σ_{k ∣ n} λ(k)`: the weight of all dilation edges ending at `n`. -/
def inDegree (lam : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ n.divisors, lam k

/-- The out-degree `Σ_{k ≤ M} λ(k)/k` of a vertex with `⌊N/n⌋ = M`. -/
def outDegree (lam : ℕ → ℝ) (M : ℕ) : ℝ := ∑ k ∈ Icc 1 M, lam k / k

/-- The degree diagonal `Σ_n F(n)²/n (out(⌊N/n⌋) + in(n))`. -/
def degreeDiagonal (lam : ℕ → ℝ) (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, F n ^ 2 / n * (outDegree lam (N / n) + inDegree lam n)

theorem dilationForm_vonMangoldt (N : ℕ) (F : ℕ → ℝ) :
    dilationForm (fun k => Λ k) N F = primeDilationForm N F := rfl

theorem dilationEnergy_vonMangoldt (N : ℕ) (F : ℕ → ℝ) :
    dilationEnergy (fun k => Λ k) N F = jumpEnergy N F := rfl

theorem inDegree_vonMangoldt (n : ℕ) : inDegree (fun k => Λ k) n = Real.log n :=
  vonMangoldt_sum

theorem outDegree_vonMangoldt (M : ℕ) : outDegree (fun k => Λ k) M = mertensSum M := rfl

theorem degreeDiagonal_vonMangoldt (N : ℕ) (F : ℕ → ℝ) :
    degreeDiagonal (fun k => Λ k) N F = mertensDiagonal N F := by
  simp only [degreeDiagonal, inDegree_vonMangoldt, outDegree_vonMangoldt, mertensDiagonal]

/-- The target half: grouping `kn = m` collects the in-degree of `m`. -/
theorem sum_dilation_target_eq_inDegree (lam : ℕ → ℝ) (N : ℕ) (G : ℕ → ℝ) :
    ∑ p ∈ dilationPairs N, lam p.1 / p.1 * (G (p.1 * p.2) / p.2) =
      ∑ m ∈ Icc 1 N, G m / m * inDegree lam m := by
  have hset : dilationPairs N = (Icc 1 N).biUnion Nat.divisorsAntidiagonal := by
    ext ⟨k, n⟩
    simp only [mem_dilationPairs, mem_biUnion, mem_Icc, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨hk, hn, hkn⟩
      exact ⟨k * n, ⟨Nat.mul_pos hk hn, hkn⟩, rfl, (Nat.mul_pos hk hn).ne'⟩
    · rintro ⟨m, ⟨hm1, hmN⟩, hkn, -⟩
      have hk : k ≠ 0 := by rintro rfl; simp at hkn; omega
      have hn : n ≠ 0 := by rintro rfl; simp at hkn; omega
      exact ⟨Nat.one_le_iff_ne_zero.mpr hk, Nat.one_le_iff_ne_zero.mpr hn, hkn ▸ hmN⟩
  rw [hset, sum_biUnion]
  · refine sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := by simp only [mem_Icc] at hm; omega
    have hterm : ∀ p ∈ m.divisorsAntidiagonal,
        lam p.1 / p.1 * (G (p.1 * p.2) / p.2) = G m / m * lam p.1 := by
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      have h1 : (p.1 : ℝ) ≠ 0 := by
        have : p.1 ≠ 0 := fun h => by simp [h] at hp; exact hm0 hp.1.symm
        exact_mod_cast this
      have h2 : (p.2 : ℝ) ≠ 0 := by
        have : p.2 ≠ 0 := fun h => by simp [h] at hp; exact hm0 hp.1.symm
        exact_mod_cast this
      have hm : (m : ℝ) = p.1 * p.2 := by rw [← hp.1]; push_cast; ring
      rw [hp.1, hm]
      field_simp
    rw [sum_congr rfl hterm, ← mul_sum, Nat.sum_divisorsAntidiagonal (fun a _ => lam a), inDegree]
  · intro m _ m' _ hmm'
    refine Finset.disjoint_left.mpr fun p hp hp' => hmm' ?_
    rw [Nat.mem_divisorsAntidiagonal] at hp hp'
    exact hp.1.symm.trans hp'.1

/-- **Polarization for every weight**: `P^λ_N = degree diagonal − J^λ_N`. -/
theorem dilationForm_eq (lam : ℕ → ℝ) (N : ℕ) (F : ℕ → ℝ) :
    dilationForm lam N F = degreeDiagonal lam N F - dilationEnergy lam N F := by
  have hpol : ∀ p ∈ dilationPairs N, lam p.1 / p.1 * (2 * F p.2 * F (p.1 * p.2) / p.2) =
      lam p.1 / p.1 * (F p.2 ^ 2 / p.2) + lam p.1 / p.1 * (F (p.1 * p.2) ^ 2 / p.2) -
        lam p.1 / p.1 * ((F (p.1 * p.2) - F p.2) ^ 2 / p.2) := fun p _ => by ring
  have hsrc : ∑ p ∈ dilationPairs N, lam p.1 / p.1 * (F p.2 ^ 2 / p.2) =
      ∑ n ∈ Icc 1 N, F n ^ 2 / n * outDegree lam (N / n) := by
    rw [sum_dilationPairs_eq N (fun k n => lam k / k * (F n ^ 2 / n))]
    refine sum_congr rfl fun n _ => ?_
    simp only [outDegree, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [dilationForm, sum_congr rfl hpol, sum_sub_distrib, sum_add_distrib, hsrc,
    sum_dilation_target_eq_inDegree lam N (fun m => F m ^ 2), dilationEnergy, degreeDiagonal,
    ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  ring

/-! ### Stars -/

/-- Restriction of a packet to the star of `d` (the multiples of `d`). -/
def starRestrict (d : ℕ) (F : ℕ → ℝ) (n : ℕ) : ℝ := if d ∣ n then F n else 0

/-- Pullback of a packet along `m ↦ dm`: the star of `d` read at horizon `⌊N/d⌋`. -/
def starPullback (d : ℕ) (F : ℕ → ℝ) (m : ℕ) : ℝ := F (d * m)

/-- The boundary flux into the star of `d` at `dm`: `in(dm) − in(m)`. -/
def starFlux (lam : ℕ → ℝ) (d m : ℕ) : ℝ := inDegree lam (d * m) - inDegree lam m

/-- Sums over the vertices of a star are sums over the lower horizon. -/
theorem sum_Icc_star {d : ℕ} (hd : 0 < d) (N : ℕ) (f : ℕ → ℝ) (hf : ∀ n, ¬ d ∣ n → f n = 0) :
    ∑ n ∈ Icc 1 N, f n = ∑ a ∈ Icc 1 (N / d), f (d * a) := by
  rw [← sum_filter_of_ne (p := fun n => d ∣ n) fun n _ h => by_contra fun hn => h (hf n hn)]
  refine sum_nbij' (fun n => n / d) (fun a => d * a) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, hN⟩, c, rfl⟩ := hn
    rw [mem_Icc, Nat.mul_div_cancel_left c hd, Nat.le_div_iff_mul_le hd]
    constructor
    · rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp at h1
      · exact hc
    · rw [mul_comm]; exact hN
  · intro a ha
    simp only [mem_Icc] at ha
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨Nat.mul_pos hd ha.1, ?_⟩, dvd_mul_right d a⟩
    rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd).mp ha.2
  · intro n hn
    simp only [mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro a _
    exact Nat.mul_div_cancel_left a hd
  · intro n hn
    simp only [mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- Dilation pairs ending in a star are the dilation pairs of the lower horizon. -/
theorem sum_dilationPairs_star {d : ℕ} (hd : 0 < d) (N : ℕ) (g : ℕ × ℕ → ℝ)
    (hg : ∀ p : ℕ × ℕ, ¬ d ∣ p.2 → g p = 0) :
    ∑ p ∈ dilationPairs N, g p = ∑ q ∈ dilationPairs (N / d), g (q.1, d * q.2) := by
  rw [← sum_filter_of_ne (p := fun p : ℕ × ℕ => d ∣ p.2)
    fun p _ h => by_contra fun hn => h (hg p hn)]
  refine sum_nbij' (fun p => (p.1, p.2 / d)) (fun q => (q.1, d * q.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_dilationPairs] at hp
    obtain ⟨⟨h1, h2, hN⟩, c, hc⟩ := hp
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with rfl | hc0
      · simp at hc; omega
      · exact hc0
    simp only [mem_dilationPairs, hc, Nat.mul_div_cancel_left c hd]
    refine ⟨h1, hc1, (Nat.le_div_iff_mul_le hd).mpr ?_⟩
    rw [hc] at hN
    calc p.1 * c * d = p.1 * (d * c) := by ring
      _ ≤ N := hN
  · intro q hq
    simp only [mem_dilationPairs] at hq
    simp only [mem_filter, mem_dilationPairs]
    refine ⟨⟨hq.1, Nat.mul_pos hd hq.2.1, ?_⟩, dvd_mul_right d q.2⟩
    have := (Nat.le_div_iff_mul_le hd).mp hq.2.2
    calc q.1 * (d * q.2) = q.1 * q.2 * d := by ring
      _ ≤ N := this
  · intro p hp
    simp only [mem_filter] at hp
    simp only [Nat.mul_div_cancel' hp.2]
  · intro q _
    simp only [Nat.mul_div_cancel_left q.2 hd]
  · intro p hp
    simp only [mem_filter] at hp
    simp only [Nat.mul_div_cancel' hp.2]

/-- **The dilation form of a star is the form of the lower horizon**, for every weight:
`P^λ_N(F·1_{dℕ}) = (1/d) P^λ_{⌊N/d⌋}(F(d·))`. -/
theorem dilationForm_starRestrict (lam : ℕ → ℝ) {d : ℕ} (hd : 0 < d) (N : ℕ) (F : ℕ → ℝ) :
    dilationForm lam N (starRestrict d F) =
      (1 / d) * dilationForm lam (N / d) (starPullback d F) := by
  rw [dilationForm, sum_dilationPairs_star hd N]
  · rw [dilationForm, mul_sum]
    refine sum_congr rfl fun q _ => ?_
    have hdd : d ∣ d * q.2 := dvd_mul_right d q.2
    have hkd : d ∣ q.1 * (d * q.2) := dvd_mul_of_dvd_right hdd q.1
    simp only [starRestrict, starPullback, if_pos hdd, if_pos hkd,
      show q.1 * (d * q.2) = d * (q.1 * q.2) by ring]
    push_cast
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    by_cases hq : (q.2 : ℝ) = 0
    · simp [hq]
    · field_simp
  · intro p hp
    simp [starRestrict, if_neg hp]

/-- **The degree diagonal of a star** is the lower-horizon diagonal plus the boundary flux. -/
theorem degreeDiagonal_starRestrict (lam : ℕ → ℝ) {d : ℕ} (hd : 0 < d) (N : ℕ) (F : ℕ → ℝ) :
    degreeDiagonal lam N (starRestrict d F) =
      (1 / d) * (degreeDiagonal lam (N / d) (starPullback d F) +
        ∑ a ∈ Icc 1 (N / d), starPullback d F a ^ 2 / a * starFlux lam d a) := by
  rw [degreeDiagonal, sum_Icc_star hd N]
  · rw [degreeDiagonal, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    simp only [starRestrict, starPullback, if_pos (dvd_mul_right d a), starFlux,
      Nat.div_div_eq_div_mul, mul_comm d a]
    push_cast
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [mul_comm a d]
    by_cases ha : (a : ℝ) = 0
    · simp [ha]
    · field_simp
      ring
  · intro n hn
    simp [starRestrict, if_neg hn]

/-- **The dilation energy of a star** is the lower-horizon energy plus the boundary flux: the
edges entering the star from outside carry exactly the flux `in(dm) − in(m)`. -/
theorem dilationEnergy_starRestrict (lam : ℕ → ℝ) {d : ℕ} (hd : 0 < d) (N : ℕ) (F : ℕ → ℝ) :
    dilationEnergy lam N (starRestrict d F) =
      (1 / d) * (dilationEnergy lam (N / d) (starPullback d F) +
        ∑ a ∈ Icc 1 (N / d), starPullback d F a ^ 2 / a * starFlux lam d a) := by
  have h1 := dilationForm_eq lam N (starRestrict d F)
  have h2 := dilationForm_eq lam (N / d) (starPullback d F)
  rw [dilationForm_starRestrict lam hd, degreeDiagonal_starRestrict lam hd] at h1
  have : dilationEnergy lam N (starRestrict d F) =
      (1 / d) * (degreeDiagonal lam (N / d) (starPullback d F) +
        ∑ a ∈ Icc 1 (N / d), starPullback d F a ^ 2 / a * starFlux lam d a) -
      (1 / d) * dilationForm lam (N / d) (starPullback d F) := by linarith
  rw [this, h2]
  ring

/-! ### Weil's weight: the flux is `log d` -/

/-- **The boundary flux of `Λ` is `log d` at every vertex of the star**, because `Λ ∗ 1 = log`. -/
theorem starFlux_vonMangoldt {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    starFlux (fun k => Λ k) d m = Real.log d := by
  rw [starFlux, inDegree_vonMangoldt, inDegree_vonMangoldt, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hd.ne') (by exact_mod_cast hm.ne')]
  ring

/-- The flux sum of `Λ` is `log d` times the star mass. -/
theorem sum_starFlux_vonMangoldt {d : ℕ} (hd : 0 < d) (M : ℕ) (G : ℕ → ℝ) :
    ∑ a ∈ Icc 1 M, G a ^ 2 / a * starFlux (fun k => Λ k) d a =
      Real.log d * ∑ a ∈ Icc 1 M, G a ^ 2 / a := by
  rw [mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [starFlux_vonMangoldt hd (by simp only [mem_Icc] at ha; omega)]
  ring

/-- **Jump energy of a star**: `J_N(F·1_{dℕ}) = (1/d)(J_{⌊N/d⌋}(F(d·)) + log d · Σ F(da)²/a)`. -/
theorem jumpEnergy_starRestrict {d : ℕ} (hd : 0 < d) (N : ℕ) (F : ℕ → ℝ) :
    jumpEnergy N (starRestrict d F) =
      (1 / d) * (jumpEnergy (N / d) (starPullback d F) +
        Real.log d * ∑ a ∈ Icc 1 (N / d), starPullback d F a ^ 2 / a) := by
  rw [← dilationEnergy_vonMangoldt, dilationEnergy_starRestrict _ hd, sum_starFlux_vonMangoldt hd]
  rfl

/-- **Mertens diagonal of a star**: the lower-horizon diagonal plus the same `log d` times mass. -/
theorem mertensDiagonal_starRestrict {d : ℕ} (hd : 0 < d) (N : ℕ) (F : ℕ → ℝ) :
    mertensDiagonal N (starRestrict d F) =
      (1 / d) * (mertensDiagonal (N / d) (starPullback d F) +
        Real.log d * ∑ a ∈ Icc 1 (N / d), starPullback d F a ^ 2 / a) := by
  rw [← degreeDiagonal_vonMangoldt, degreeDiagonal_starRestrict _ hd, sum_starFlux_vonMangoldt hd,
    degreeDiagonal_vonMangoldt]

/-- The prime dilation form of a star is the prime dilation form of the lower horizon. -/
theorem primeDilationForm_starRestrict {d : ℕ} (hd : 0 < d) (N : ℕ) (F : ℕ → ℝ) :
    primeDilationForm N (starRestrict d F) =
      (1 / d) * primeDilationForm (N / d) (starPullback d F) :=
  dilationForm_starRestrict _ hd N F

/-! ### Weil's coordinates -/

/-- **Weil's prime kernel depends only on ratios.** -/
theorem weilPrimeKernel_mul_mul {d : ℕ} (hd : 0 < d) (m n : ℕ) :
    weilPrimeKernel (d * m) (d * n) = weilPrimeKernel m n := by
  have hdvd : ∀ a b : ℕ, d * a ∣ d * b ↔ a ∣ b := fun a b => Nat.mul_dvd_mul_iff_left hd
  have hne : ∀ a b : ℕ, d * a ≠ d * b ↔ a ≠ b := fun a b =>
    ⟨fun h h' => h (by rw [h']), fun h h' => h (Nat.eq_of_mul_eq_mul_left hd h')⟩
  have hdiv : ∀ a b : ℕ, d * b / (d * a) = b / a := fun a b => Nat.mul_div_mul_left b a hd
  simp only [weilPrimeKernel, hdvd, hne, hdiv]

/-- **The atomic Weil prime form of a star is the form of the lower horizon.** -/
theorem atomicWeilForm_starRestrict {d : ℕ} (hd : 0 < d) (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N (starRestrict d x) = atomicWeilForm (N / d) (starPullback d x) := by
  rw [atomicWeilForm, sum_Icc_star hd N]
  · rw [atomicWeilForm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_Icc_star hd N]
    · refine sum_congr rfl fun b _ => ?_
      simp only [starRestrict, starPullback, if_pos (dvd_mul_right d a),
        if_pos (dvd_mul_right d b), weilPrimeKernel_mul_mul hd]
    · intro n hn
      simp [starRestrict, if_neg hn]
  · intro n hn
    refine sum_eq_zero fun m _ => ?_
    simp [starRestrict, if_neg hn]

/-- The Euclidean mass of a star is the mass of its pullback. -/
theorem sum_sq_starRestrict {d : ℕ} (hd : 0 < d) (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, starRestrict d x n ^ 2 = ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 := by
  rw [sum_Icc_star hd N]
  · simp only [starRestrict, starPullback, if_pos (dvd_mul_right _ _)]
  · intro n hn
    simp [starRestrict, if_neg hn]

/-- The renormalized prime form `(log N − γ)|x|² − P_N(x)`. -/
def renormalizedPrimeForm (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  (Real.log N - Real.eulerMascheroniConstant) * ∑ n ∈ Icc 1 N, x n ^ 2 - atomicWeilForm N x

/-- **The running counterterm pays the boundary flux.** On the star of `d` the renormalized prime
form is the renormalized form at horizon `⌊N/d⌋` plus `(log N − log ⌊N/d⌋)` times the mass. -/
theorem renormalizedPrimeForm_starRestrict {d : ℕ} (hd : 0 < d) (N : ℕ) (x : ℕ → ℝ) :
    renormalizedPrimeForm N (starRestrict d x) =
      renormalizedPrimeForm (N / d) (starPullback d x) +
        (Real.log N - Real.log (N / d : ℕ)) * ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 := by
  rw [renormalizedPrimeForm, renormalizedPrimeForm, atomicWeilForm_starRestrict hd,
    sum_sq_starRestrict hd]
  ring

/-- The counterterm shift of a star is at least `log d`. -/
theorem log_le_log_sub_log_div {d N : ℕ} (hd : 0 < d) (hN : d ≤ N) :
    Real.log d ≤ Real.log N - Real.log (N / d : ℕ) := by
  have hq : 0 < N / d := Nat.div_pos hN hd
  have hle : ((N / d : ℕ) : ℝ) * d ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
  have hqpos : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast hq
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have := Real.log_le_log (mul_pos hqpos hdpos) hle
  rw [Real.log_mul hqpos.ne' hdpos.ne'] at this
  linarith

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
