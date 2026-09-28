import GaloisForLFunctions.RHTower.MobiusPrimeSemiprimeCellMatching

/-!
# Two-layer compensation: primes and semiprimes together

In each cell of width `h = R/⌊(log R)^B⌋` the squarefree semiprimes number at most
`h/log R · (log log R + K)`, while the triprimes `qpr`, `q ∈ {2, 3, 5}`, `5 < p < r` primes, number
at least `(61/62)(1/2 + 1/3 + 1/5) h/log R · (log log R - K') = (61/60) h/log R · (log log R - K')`.
After the primes have been matched to semiprimes, the unused semiprimes are matched cellwise to
triprimes.  Every prime and every squarefree semiprime of `(R, 2R]` is then paired with an
opposite-sign atom of its own cell, and uniformly in `0 ≤ δ ≤ 1`

`‖T_R‖_δ² ≤ C R^{1-δ} (log log R)²/(log R)^{2B+2}`.                              (3)
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.PrimeCells

open RHTower.CubicGamma

/-- The triprimes `qpr ∈ (u, v]`, `q ∈ {2, 3, 5}`, `5 < p ≤ √(u/q) < r` primes. -/
def triTargets (u v : ℝ) : Finset ℕ :=
  ({2, 3, 5} : Finset ℕ).biUnion fun q => triprimeTargets q u v

theorem mem_triTargets {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {n : ℕ} (hn : n ∈ triTargets u v) :
    ∃ q p r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ p.Prime ∧ r.Prime ∧ 5 < p ∧ p < r ∧ n = q * p * r ∧
      u < n ∧ (n : ℝ) ≤ v := by
  unfold triTargets at hn
  obtain ⟨q, hq, hn⟩ := mem_biUnion.mp hn
  obtain ⟨hqp, hq2, -⟩ := small_cofactor_cases hq
  obtain ⟨p, r, hp, hr, h5, hpr, he, hlt, hle⟩ := mem_triprimeTargets (by omega) hu hv hn
  exact ⟨q, p, r, by simpa using hq, hp, hr, h5, hpr, he, hlt, hle⟩

/-- `qpr = q'p'r'` with `q, q' ≤ 5 < p, p'` forces `q = q'`. -/
theorem small_factor_eq {q p r q' p' r' : ℕ} (hq : q.Prime) (hq' : q'.Prime) (hp' : p'.Prime)
    (hr' : r'.Prime) (hq5 : q ≤ 5) (h5 : 5 < p') (hpr' : p' < r')
    (h : q * p * r = q' * p' * r') : q = q' := by
  have h1 : q ∣ q' * p' * r' := h ▸ (dvd_mul_right q p).mul_right r
  rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
    · exact (Nat.prime_dvd_prime_iff_eq hq hq').mp h3
    · have := (Nat.prime_dvd_prime_iff_eq hq hp').mp h3; omega
  · have := (Nat.prime_dvd_prime_iff_eq hq hr').mp h2; omega

/-- The three triprime families are disjoint, so the target count is their sum. -/
theorem card_triTargets {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (triTargets u v).card = ∑ q ∈ ({2, 3, 5} : Finset ℕ), (triprimeTargets q u v).card := by
  unfold triTargets
  rw [card_biUnion]
  intro q hq q' hq' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro n hn hn'
  obtain ⟨hqp, hq2, hq5⟩ := small_cofactor_cases hq
  obtain ⟨hqp', hq2', -⟩ := small_cofactor_cases hq'
  obtain ⟨p, r, hp, hr, h5, hpr, he, -⟩ := mem_triprimeTargets (by omega) hu hv hn
  obtain ⟨p', r', hp', hr', h5', hpr', he', -⟩ := mem_triprimeTargets (by omega) hu hv hn'
  exact hne (small_factor_eq hqp hqp' hp' hr' hq5 h5' hpr' (he ▸ he'))

/-- `(61/62)(1/2 + 1/3 + 1/5) = 61/60`: the triprime supply beats the semiprime demand once
`ℓ ≥ 60 K₁ + 61 K₂`. -/
theorem triTargets_card_ge {u v L ℓ K₁ K₂ : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hL : 0 < L)
    (hℓ : 60 * K₁ + 61 * K₂ ≤ ℓ)
    (hlow : ∀ q : ℕ, q ∈ ({2, 3, 5} : Finset ℕ) →
      (1 - 1 / 62) * (v - u) / (q * L) * (ℓ - K₂) ≤ ((triprimeTargets q u v).card : ℝ)) :
    (v - u) / L * (ℓ + K₁) ≤ ((triTargets u v).card : ℝ) := by
  rw [card_triTargets hu (by linarith)]
  push_cast
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have h2 := hlow 2 (by decide)
  have h3 := hlow 3 (by decide)
  have h5 := hlow 5 (by decide)
  push_cast at h2 h3 h5
  have hq : 0 ≤ (v - u) / L := div_nonneg (by linarith) hL.le
  have e : (1 - 1 / 62) * (v - u) / (2 * L) * (ℓ - K₂) +
      (1 - 1 / 62) * (v - u) / (3 * L) * (ℓ - K₂) + (1 - 1 / 62) * (v - u) / (5 * L) * (ℓ - K₂) =
      (v - u) / L * (61 / 60 * (ℓ - K₂)) := by
    field_simp; ring
  have hk : ℓ + K₁ ≤ 61 / 60 * (ℓ - K₂) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hk hq]

/-- **Cellwise semiprime–triprime matching at one scale.**  Given the semiprime and triprime cell
counts, every subset `S` of the squarefree semiprimes of `(R, 2R]` is matched injectively to
triprimes `qpr ∈ (R, 2R]`, `q ∈ {2,3,5}`, `5 < p < r` primes, at distance at most `2R/x`. -/
theorem exists_triprime_cell_matching_of_counts {R : ℕ} {L x ℓ K₁ K₂ : ℝ} (hR : (80 : ℝ) ≤ R)
    (hx : 1 ≤ x) (hL : 0 < L) (hℓ : 60 * K₁ + 61 * K₂ ≤ ℓ)
    (hsemi : ∀ u v : ℝ, (R : ℝ) ≤ u → u ≤ v → v ≤ 2 * R → R / x ≤ v - u →
      ((semiprimesIn u v).card : ℝ) ≤ (v - u) / L * (ℓ + K₁))
    (htri : ∀ q : ℕ, 2 ≤ q → q ≤ 5 → ∀ u v : ℝ, (R : ℝ) ≤ u → u ≤ v → v ≤ 2 * R →
      R / x ≤ v - u → (1 - 1 / 62) * (v - u) / (q * L) * (ℓ - K₂) ≤
        ((triprimeTargets q u v).card : ℝ))
    (S : Finset ℕ) (hS : S ⊆ semiprimesIn R (2 * R)) :
    ∃ ψ : ℕ → ℕ, Set.InjOn ψ ↑S ∧
      ∀ m ∈ S, (R : ℝ) < ψ m ∧ (ψ m : ℝ) ≤ 2 * R ∧
        (∃ q p r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ p.Prime ∧ r.Prime ∧ 5 < p ∧ p < r ∧
          ψ m = q * p * r) ∧
        |(ψ m : ℝ) - m| ≤ 2 * R / x := by
  classical
  have hR0 : (0 : ℝ) < R := by linarith
  obtain ⟨hJ1, hhlow, hhup, hJh⟩ := cell_scale hR0 hx
  obtain ⟨h, hhdef⟩ : ∃ h : ℝ, h = (R : ℝ) / ⌊x⌋₊ := ⟨_, rfl⟩
  rw [← hhdef] at hhlow hhup hJh
  have hJ0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hJ1
  have hh : 0 < h := by rw [hhdef]; positivity
  have hcell : ∀ i < ⌊x⌋₊, (R : ℝ) ≤ R + i * h ∧ (R : ℝ) + i * h ≤ R + (i + 1) * h ∧
      (R : ℝ) + (i + 1) * h ≤ 2 * R ∧ (R : ℝ) / x ≤ R + (i + 1) * h - (R + i * h) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ ⌊x⌋₊ := by exact_mod_cast hi
    have h1 : (0 : ℝ) ≤ i * h := by positivity
    have h2 : ((i : ℝ) + 1) * h ≤ ⌊x⌋₊ * h := by gcongr
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hSmem : ∀ m ∈ S, (R : ℝ) < m ∧ (m : ℝ) ≤ 2 * R ∧
      ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p < r ∧ m = p * r :=
    fun m hm => (mem_semiprimesIn (by positivity) (by positivity)).mp (hS hm)
  have hSc : ∀ m ∈ S, cellIndex R h m < ⌊x⌋₊ := by
    intro m hm
    obtain ⟨h1, h2, -⟩ := hSmem m hm
    exact cellIndex_lt hh h1 (by rw [hJh]; linarith)
  set T := (range ⌊x⌋₊).biUnion fun i => triTargets ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)
    with hT
  have hcount : ∀ i, (S.filter (cellIndex R h · = i)).card ≤
      (T.filter (cellIndex R h · = i)).card := by
    intro i
    by_cases hi : i < ⌊x⌋₊
    · obtain ⟨hu, huv, hv, hgap⟩ := hcell i hi
      have hsub1 : S.filter (cellIndex R h · = i) ⊆
          semiprimesIn ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h) := by
        intro m hm
        obtain ⟨hm, hmi⟩ := mem_filter.mp hm
        obtain ⟨h1, -, hform⟩ := hSmem m hm
        obtain ⟨h3, h4⟩ := cellIndex_spec hh h1
        rw [hmi] at h3 h4
        exact (mem_semiprimesIn (by linarith) (by linarith)).mpr ⟨h3, h4, hform⟩
      have hsub2 : triTargets ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h) ⊆
          T.filter (cellIndex R h · = i) := by
        intro n hn
        obtain ⟨-, -, -, -, -, -, -, -, -, h3, h4⟩ :=
          mem_triTargets (by linarith) (by linarith) hn
        exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_range.mpr hi, hn⟩, cellIndex_eq hh h3 h4⟩
      have hle : ((semiprimesIn ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card : ℝ) ≤
          (triTargets ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card :=
        (hsemi _ _ hu huv hv hgap).trans (triTargets_card_ge (by linarith) huv hL hℓ
          fun q hq => htri q (small_cofactor_cases hq).2.1 (small_cofactor_cases hq).2.2 _ _
            hu huv hv hgap)
      have hle' : (semiprimesIn ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card ≤
          (triTargets ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card := by
        exact_mod_cast hle
      exact (card_le_card hsub1).trans (hle'.trans (card_le_card hsub2))
    · have : S.filter (cellIndex R h · = i) = ∅ := by
        refine filter_eq_empty_iff.mpr fun m hm hmi => hi ?_
        rw [← hmi]; exact hSc m hm
      rw [this]; exact Nat.zero_le _
  obtain ⟨ψ, hinj, hψ⟩ := exists_cellwise_injOn _ _ T hcount
  refine ⟨ψ, hinj, fun m hm => ?_⟩
  obtain ⟨hψT, hψc⟩ := hψ m hm
  obtain ⟨i, hi, hn⟩ := mem_biUnion.mp hψT
  have hi' := mem_range.mp hi
  obtain ⟨hu, huv, hv, -⟩ := hcell i hi'
  obtain ⟨q, p, r, hq, hp, hr, h5, hpr, he, hlt, hle⟩ :=
    mem_triTargets (by linarith) (by linarith) hn
  have hci : cellIndex R h (ψ m) = i := cellIndex_eq hh hlt hle
  obtain ⟨h1, -, -⟩ := hSmem m hm
  obtain ⟨h3, h4⟩ := cellIndex_spec hh h1
  rw [← hψc, hci] at h3 h4
  refine ⟨by linarith, hle.trans hv, ⟨q, p, r, hq, hp, hr, h5, hpr, he⟩, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- `μ(pr) = 1` for primes `p < r`. -/
theorem moebius_mul_primes {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    μ (p * r) = 1 := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    ((Nat.coprime_primes hp hr).mpr hpr.ne), ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hr]
  norm_num

/-- `μ(qpr) = -1` for primes `q < p < r`. -/
theorem moebius_mul_three_primes {q p r : ℕ} (hq : q.Prime) (hp : p.Prime) (hr : r.Prime)
    (hqp : q < p) (hpr : p < r) : μ (q * p * r) = -1 := by
  have hcop : Nat.Coprime q (p * r) :=
    Nat.Coprime.mul_right ((Nat.coprime_primes hq hp).mpr hqp.ne)
      ((Nat.coprime_primes hq hr).mpr (by omega))
  rw [mul_assoc, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    moebius_mul_primes hp hr hpr, ArithmeticFunction.moebius_apply_prime hq]
  norm_num

/-- The reversed orientation of `gammaNorm_matched_le`. -/
theorem gammaNorm_matched_le' {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {R D : ℝ} (hR : 0 < R)
    (P : Finset ℕ) (φ : ℕ → ℕ) (hP : ∀ p ∈ P, R ≤ p ∧ (p : ℝ) ≤ 2 * R)
    (hφ : ∀ p ∈ P, R ≤ φ p ∧ (φ p : ℝ) ≤ 2 * R) (hD : ∀ p ∈ P, |(φ p : ℝ) - p| ≤ D) :
    gammaNorm δ (fun t => ∑ p ∈ P, (atom p t - atom (φ p) t)) ≤
      P.card * (4 * jetConst 1 * D * R ^ (-(3 + δ) / 2)) := by
  have hδ : 0 < 5 + δ := by linarith
  have hfin : GammaFinite δ (fun t => ∑ p ∈ P, (atom (φ p) t - atom p t)) :=
    GammaFinite.sum P fun p hp =>
      (gammaFinite_atom hδ (by linarith [(hφ p hp).1])).sub
        (gammaFinite_atom hδ (by linarith [(hP p hp).1]))
  have e : (fun t => ∑ p ∈ P, (atom p t - atom (φ p) t)) =
      fun t => -∑ p ∈ P, (atom (φ p) t - atom p t) := by
    funext t; rw [← sum_neg_distrib]; exact sum_congr rfl fun p _ => by ring
  rw [e, gammaNorm_neg hδ hfin]
  exact gammaNorm_matched_le hδ0 hδ1 hR P φ hP hφ hD

/-- **Two-layer literal identity.**  With `φ(P) ⊆ SP`, the prime dipoles and the dipoles of the
unused semiprimes are the literal Möbius subsum over primes, semiprimes and triprime targets. -/
theorem two_layer_sum_eq_literal (P SP : Finset ℕ) (φ ψ : ℕ → ℕ) (hφinj : Set.InjOn φ ↑P)
    (hφSP : P.image φ ⊆ SP) (hPSP : Disjoint P SP)
    (hT : Disjoint (P ∪ SP) ((SP \ P.image φ).image ψ)) (hψinj : Set.InjOn ψ ↑(SP \ P.image φ))
    (hμP : ∀ p ∈ P, μ p = -1) (hμSP : ∀ m ∈ SP, μ m = 1)
    (hμT : ∀ m ∈ SP \ P.image φ, μ (ψ m) = -1) (t : ℝ) :
    ∑ p ∈ P, (atom (φ p) t - atom p t) + ∑ m ∈ SP \ P.image φ, (atom m t - atom (ψ m) t) =
      ∑ n ∈ P ∪ SP ∪ (SP \ P.image φ).image ψ, ((μ n : ℤ) : ℝ) * atom n t := by
  rw [sum_union hT, sum_union hPSP, sum_image hψinj, ← sum_sdiff hφSP, sum_image hφinj]
  have h1 : ∑ p ∈ P, ((μ p : ℤ) : ℝ) * atom p t = -∑ p ∈ P, atom p t := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun p hp => by rw [hμP p hp]; push_cast; ring
  have h2 : ∑ m ∈ SP \ P.image φ, ((μ m : ℤ) : ℝ) * atom m t = ∑ m ∈ SP \ P.image φ, atom m t :=
    sum_congr rfl fun m hm => by rw [hμSP m (mem_sdiff.mp hm).1]; push_cast; ring
  have h3 : ∑ p ∈ P, ((μ (φ p) : ℤ) : ℝ) * atom (φ p) t = ∑ p ∈ P, atom (φ p) t :=
    sum_congr rfl fun p hp => by
      rw [hμSP (φ p) (hφSP (mem_image_of_mem φ hp))]; push_cast; ring
  have h4 : ∑ m ∈ SP \ P.image φ, ((μ (ψ m) : ℤ) : ℝ) * atom (ψ m) t =
      -∑ m ∈ SP \ P.image φ, atom (ψ m) t := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun m hm => by rw [hμT m hm]; push_cast; ring
  rw [h1, h2, h3, h4, sum_sub_distrib, sum_sub_distrib]
  ring

/-- **Two-layer compensation (3).**  Fix `B > 0`.  For all large `R` every prime `p ∈ (R, 2R]` is
matched injectively to a semiprime `φ(p) = qr` of `(R, 2R]`, and every squarefree semiprime of
`(R, 2R]` not of the form `φ(p)` is matched injectively to a triprime `ψ(m) = qpr ∈ (R, 2R]`,
`q ∈ {2,3,5}`, `5 < p < r` primes; all displacements are at most `2R/(log R)^B`.  The dipole sum
`T_R` is the literal Möbius subsum over the disjoint primes, semiprimes and triprime targets of
`(R, 2R]`, so each of its atoms occurs exactly once in the source at every cutoff `N ≥ 2R`, and
uniformly in
`0 ≤ δ ≤ 1`: `‖T_R‖_δ² ≤ C R^{1-δ} (log log R)²/(log R)^{2B+2}`. -/
theorem exists_two_layer_matching {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ φ ψ : ℕ → ℕ,
        Set.InjOn φ ↑(windowPrimes R (2 * R)) ∧
        (∀ p ∈ windowPrimes R (2 * R), φ p ∈ semiprimesIn R (2 * R) ∧
          (∃ q r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧ φ p = q * r) ∧
          |(φ p : ℝ) - p| ≤ 2 * R / Real.log R ^ B) ∧
        Set.InjOn ψ ↑(semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ) ∧
        (∀ m ∈ semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ,
          R < ψ m ∧ ψ m ≤ 2 * R ∧
          (∃ q p r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ p.Prime ∧ r.Prime ∧ 5 < p ∧ p < r ∧
            ψ m = q * p * r) ∧
          |(ψ m : ℝ) - m| ≤ 2 * R / Real.log R ^ B) ∧
        Disjoint (windowPrimes R (2 * R) ∪ semiprimesIn R (2 * R))
          ((semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ).image ψ) ∧
        windowPrimes R (2 * R) ∪ semiprimesIn R (2 * R) ∪
          (semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ).image ψ ⊆ Ioc R (2 * R) ∧
        (∀ t : ℝ, ∑ p ∈ windowPrimes R (2 * R), (atom (φ p) t - atom p t) +
            ∑ m ∈ semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ,
              (atom m t - atom (ψ m) t) =
          ∑ n ∈ windowPrimes R (2 * R) ∪ semiprimesIn R (2 * R) ∪
              (semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ).image ψ,
            ((μ n : ℤ) : ℝ) * atom n t) ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ p ∈ windowPrimes R (2 * R), (atom (φ p) t - atom p t) +
            ∑ m ∈ semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ,
              (atom m t - atom (ψ m) t)) ^ 2 ≤
            C * (R : ℝ) ^ (1 - δ) * Real.log (Real.log R) ^ 2 / Real.log R ^ (2 * B + 2) := by
  classical
  obtain ⟨C₁, -, R₀₁, h1⟩ := exists_prime_semiprime_matching hB
  obtain ⟨R₁, -, hup⟩ := exists_card_windowPrimes_le B (ε := 1 / 100) (by norm_num)
  obtain ⟨K₁, R₃, -, hsemi⟩ := exists_card_semiprimesIn_le B
  obtain ⟨K₂, R₄, -, htri⟩ := exists_card_triprimeTargets_ge B (ε := 1 / 62) (by norm_num)
    (by norm_num)
  have hev : ∀ᶠ R : ℝ in atTop, R₁ ≤ R ∧ R₃ ≤ R ∧ R₄ ≤ R ∧ 80 ≤ R ∧ 1 ≤ Real.log R ∧
      60 * K₁ + 61 * K₂ ≤ Real.log (Real.log R) ∧ K₁ + 2 ≤ Real.log (Real.log R) :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((eventually_ge_atTop _).and ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _).and
          ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _))))))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  have hc := jetConst_nonneg 1
  refine ⟨64 * jetConst 1 ^ 2 * 2 ^ 2 + 1, by positivity, max R₀₁ ⌈X⌉₊, fun R hR => ?_⟩
  have hRX : X ≤ (R : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast le_of_max_le_right hR)
  obtain ⟨hR1, hR3, hR4, hR80, hL1, hℓ, hℓ2⟩ := hX R hRX
  obtain ⟨φ, hφinj, hφ, hφd, hμφ, hdisjφ, -, -⟩ := h1 R (le_of_max_le_left hR)
  have hR0 : (0 : ℝ) < R := by linarith
  have hL0 : 0 < Real.log R := by linarith
  have hx : 1 ≤ Real.log R ^ B := Real.one_le_rpow hL1 hB.le
  have hPmem : ∀ p ∈ windowPrimes R (2 * R), p.Prime ∧ (R : ℝ) < p ∧ (p : ℝ) ≤ 2 * R :=
    fun p hp => (mem_windowPrimes (by positivity) (by positivity)).mp hp
  have hSPmem : ∀ m ∈ semiprimesIn R (2 * R), (R : ℝ) < m ∧ (m : ℝ) ≤ 2 * R ∧
      ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p < r ∧ m = p * r :=
    fun m hm => (mem_semiprimesIn (by positivity) (by positivity)).mp hm
  -- `φ(p)` is a squarefree semiprime of `(R, 2R]`
  have hφSP : ∀ p ∈ windowPrimes R (2 * R), φ p ∈ semiprimesIn R (2 * R) := by
    intro p hp
    obtain ⟨h1, h2, ⟨q, r, hq, hr, h5, he⟩⟩ := hφ p hp
    have hqp : q.Prime := by rcases hq with h | h | h <;> subst h <;> norm_num
    have hq5 : q ≤ 5 := by rcases hq with h | h | h <;> omega
    exact (mem_semiprimesIn (by positivity) (by positivity)).mpr
      ⟨by exact_mod_cast h1, by exact_mod_cast h2, q, r, hqp, hr, by omega, he⟩
  obtain ⟨ψ, hψinj, hψ⟩ := exists_triprime_cell_matching_of_counts hR80 hx hL0 hℓ
    (hsemi R hR3) (fun q hq2 hq5 u v => htri R hR4 q hq2 hq5 u v)
    (semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ) sdiff_subset
  -- Möbius values
  have hμP : ∀ p ∈ windowPrimes R (2 * R), μ p = -1 := fun p hp => (hμφ p hp).1
  have hμSP : ∀ m ∈ semiprimesIn R (2 * R), μ m = 1 := by
    intro m hm
    obtain ⟨-, -, p, r, hp, hr, hpr, rfl⟩ := hSPmem m hm
    exact moebius_mul_primes hp hr hpr
  have hμT : ∀ m ∈ semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ, μ (ψ m) = -1 := by
    intro m hm
    obtain ⟨-, -, ⟨q, p, r, hq, hp, hr, h5, hpr, he⟩, -⟩ := hψ m hm
    have hqp : q.Prime := by rcases hq with h | h | h <;> subst h <;> norm_num
    have hq5 : q ≤ 5 := by rcases hq with h | h | h <;> omega
    rw [he]
    exact moebius_mul_three_primes hqp hp hr (by omega) hpr
  have hPSP : Disjoint (windowPrimes R (2 * R)) (semiprimesIn R (2 * R)) := by
    rw [disjoint_left]
    intro n hn hn'
    have := (hμP n hn).symm.trans (hμSP n hn')
    norm_num at this
  have hT : Disjoint (windowPrimes R (2 * R) ∪ semiprimesIn R (2 * R))
      ((semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ).image ψ) := by
    rw [disjoint_left]
    intro n hn hn'
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn'
    rcases mem_union.mp hn with hn | hn
    · obtain ⟨-, -, ⟨q, p, r, hq, hp, hr, h5, hpr, he⟩, -⟩ := hψ m hm
      have hn' := (hPmem _ hn).1
      rw [he] at hn'
      have hq1 : q * p ≠ 1 := by
        have := hp.two_le
        rcases hq with h | h | h <;> subst h <;> omega
      exact Nat.not_prime_mul hq1 hr.ne_one hn'
    · have := (hμT m hm).symm.trans (hμSP _ hn)
      norm_num at this
  have hψR : ∀ m ∈ semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ,
      R < ψ m ∧ ψ m ≤ 2 * R := fun m hm => by
    obtain ⟨h1, h2, -⟩ := hψ m hm
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hsub : windowPrimes R (2 * R) ∪ semiprimesIn R (2 * R) ∪
      (semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ).image ψ ⊆ Ioc R (2 * R) := by
    intro n hn
    rw [mem_Ioc]
    rcases mem_union.mp hn with hn | hn
    · rcases mem_union.mp hn with hn | hn
      · obtain ⟨-, h1, h2⟩ := hPmem n hn
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · obtain ⟨h1, h2, -⟩ := hSPmem n hn
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      exact hψR m hm
  refine ⟨φ, ψ, hφinj, fun p hp => ⟨hφSP p hp, (hφ p hp).2.2, hφd p hp⟩, hψinj,
    fun m hm => ⟨(hψR m hm).1, (hψR m hm).2, (hψ m hm).2.2⟩, hT, hsub,
    fun t => two_layer_sum_eq_literal _ _ φ ψ hφinj
      (fun n hn => by obtain ⟨p, hp, rfl⟩ := mem_image.mp hn; exact hφSP p hp) hPSP hT hψinj
      hμP hμSP hμT t, fun δ hδ0 hδ1 => ?_⟩
  -- the energy
  have hδ : 0 < 5 + δ := by linarith
  have hφR : ∀ p ∈ windowPrimes R (2 * R), (R : ℝ) < φ p ∧ (φ p : ℝ) ≤ 2 * R := fun p hp =>
    ⟨by exact_mod_cast (hφ p hp).1, by exact_mod_cast (hφ p hp).2.1⟩
  set M := semiprimesIn R (2 * R) \ (windowPrimes R (2 * R)).image φ with hM
  have hn1 := gammaNorm_matched_le hδ0 hδ1 hR0 (windowPrimes R (2 * R)) φ
    (fun p hp => ⟨(hPmem p hp).2.1.le, (hPmem p hp).2.2⟩)
    (fun p hp => ⟨(hφR p hp).1.le, (hφR p hp).2⟩) hφd
  have hn2 := gammaNorm_matched_le' hδ0 hδ1 hR0 M ψ
    (fun m hm => ⟨(hSPmem m (mem_sdiff.mp hm).1).1.le, (hSPmem m (mem_sdiff.mp hm).1).2.1⟩)
    (fun m hm => ⟨(hψ m hm).1.le, (hψ m hm).2.1⟩) (fun m hm => (hψ m hm).2.2.2)
  have hfin1 : GammaFinite δ (fun t => ∑ p ∈ windowPrimes R (2 * R), (atom (φ p) t - atom p t)) :=
    GammaFinite.sum _ fun p hp => (gammaFinite_atom hδ (by linarith [(hφR p hp).1])).sub
      (gammaFinite_atom hδ (by linarith [(hPmem p hp).2.1]))
  have hfin2 : GammaFinite δ (fun t => ∑ m ∈ M, (atom m t - atom (ψ m) t)) :=
    GammaFinite.sum _ fun m hm => (gammaFinite_atom hδ
      (by linarith [(hSPmem m (mem_sdiff.mp hm).1).1])).sub
      (gammaFinite_atom hδ (by linarith [(hψ m hm).1]))
  have hsum := gammaNorm_add_le hδ hfin1 hfin2
  -- counts: `#P + #M ≤ 2 log log R · R/log R`
  have hgap : (R : ℝ) / Real.log R ^ B ≤ 2 * R - R := by
    rw [show (2 : ℝ) * R - R = R by ring]; exact div_le_self hR0.le hx
  have hcardP : ((windowPrimes R (2 * R)).card : ℝ) ≤ 2 * R / Real.log R := by
    have := hup R hR1 R (2 * R) le_rfl (by linarith) le_rfl hgap
    calc ((windowPrimes R (2 * R)).card : ℝ) ≤ (1 + 1 / 100) * (2 * R - R) / Real.log R := this
      _ ≤ 2 * R / Real.log R := div_le_div_of_nonneg_right (by linarith) hL0.le
  have hcardM : (M.card : ℝ) ≤ R / Real.log R * (Real.log (Real.log R) + K₁) := by
    have h := hsemi R hR3 R (2 * R) le_rfl (by linarith) le_rfl hgap
    have hMc : M.card ≤ (semiprimesIn R (2 * R)).card := card_le_card sdiff_subset
    calc (M.card : ℝ) ≤ (semiprimesIn R (2 * R)).card := by exact_mod_cast hMc
      _ ≤ _ := h
      _ = R / Real.log R * (Real.log (Real.log R) + K₁) := by ring
  have hN : ((windowPrimes R (2 * R)).card : ℝ) + M.card ≤
      2 * Real.log (Real.log R) * R / Real.log R := by
    have e : 2 * Real.log (Real.log R) * R / Real.log R =
        R / Real.log R * (2 * Real.log (Real.log R)) := by ring
    have e2 : 2 * (R : ℝ) / Real.log R = R / Real.log R * 2 := by ring
    rw [e]
    rw [e2] at hcardP
    have hq : 0 ≤ (R : ℝ) / Real.log R := by positivity
    nlinarith
  have hX : gammaNorm δ (fun t => ∑ p ∈ windowPrimes R (2 * R), (atom (φ p) t - atom p t) +
      ∑ m ∈ M, (atom m t - atom (ψ m) t)) ≤
      (((windowPrimes R (2 * R)).card : ℝ) + M.card) *
        (4 * jetConst 1 * (2 * R / Real.log R ^ B) * (R : ℝ) ^ (-(3 + δ) / 2)) := by
    linarith
  have hsq := matched_energy_sq_le hR0 hL0 hc hN (gammaNorm_nonneg _ _) hX
  have hRδ : 0 ≤ (R : ℝ) ^ (1 - δ) * Real.log (Real.log R) ^ 2 / Real.log R ^ (2 * B + 2) := by
    positivity
  calc _ ≤ 64 * jetConst 1 ^ 2 * (2 * Real.log (Real.log R)) ^ 2 * (R : ℝ) ^ (1 - δ) /
        Real.log R ^ (2 * B + 2) := hsq
    _ = 64 * jetConst 1 ^ 2 * 2 ^ 2 *
        ((R : ℝ) ^ (1 - δ) * Real.log (Real.log R) ^ 2 / Real.log R ^ (2 * B + 2)) := by ring
    _ ≤ (64 * jetConst 1 ^ 2 * 2 ^ 2 + 1) *
        ((R : ℝ) ^ (1 - δ) * Real.log (Real.log R) ^ 2 / Real.log R ^ (2 * B + 2)) := by
        gcongr; linarith
    _ = _ := by ring

end RHTower.PrimeCells
