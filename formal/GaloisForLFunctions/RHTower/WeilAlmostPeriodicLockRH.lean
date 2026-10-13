import GaloisForLFunctions.RHTower.WeilRationalLockRH

/-!
# Almost-periodic locks force the Riemann hypothesis

**Theorem** (`almostPeriodicLock_riemannHypothesis`). Let `G` be a Herglotz producer for the
weights `lam` with lower-line lock

`G(1 − s) = V(s) G(s)`,   `V(s) = Σ_j c_j u_j^{−(s−½)}`,

with arbitrary positive real frequencies `u_j` and `Σ_j |c_j| max(1, u_j^{−1}) K(u_j) < ∞`. Here
`K(u) = √den(u) 8^{ω(den u)}` for rational `u` and `K(u) = 1` for irrational `u`. Then the Riemann
hypothesis holds. This closes the almost-periodic lock class: rational and irrational
frequencies, on both sides of `1`, with unbounded denominators.

**Key lemma** (`lockPer_eq_zero_of_irrational`). Irrational lock points carry no weight. Fix an
irrational point `y > 0`.
* `𝒫(y) = Σ_{n u_j = y} a(n) c_j √u_j` has period one (`lockPer_add_one`), and `|a| ≤ W`
  (`apLock_coefficients`).
* An irrational frequency meets the orbit `y + ℤ` at most once, since `(n − n')u ∈ ℤ` with
  `n ≠ n'` makes `u` rational. A rational frequency never meets it (`lockPoint_orbit_inj`).
* So the fibres over `y + k` use disjoint frequency sets, and `Σ_k S(y + k) ≤ Σ_j |c_j|`
  (`summable_orbit_fiber_norm`), where `S(t) = Σ_{n u_j = t} |c_j|`.
* `|𝒫(y)| = |𝒫(y + k)| ≤ W √(y + k) S(y + k)` (`norm_lockPer_le`). Summing,
  `Σ_k |𝒫(y)|/√(y + k) < ∞`, so `𝒫(y) = 0`.

Rational frequencies can meet an orbit infinitely often, which is why periodic and limit-periodic
coefficients survive.

**Proof of the theorem.** `apLock_coefficients` expands `a` over the lock points below one. The
key lemma removes the irrational points fibrewise (`lockExpCoeff_eq_ratPart`). What remains is the
expansion of the rational part of the lock, and the rational-lock chain
(`lockExpCoeff_eq_tsum_ratLockPart`, `summable_ratLockMass_weight`,
`limitPeriodic_producer_riemannHypothesis`) gives RH.
-/

open Complex Filter Topology Set

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral CharacterZeroPlanting

noncomputable section

/-! ## Fibres and orbits of lock points -/

/-- Over an irrational orbit `y + ℕ`, a pair is determined by its frequency index: an irrational
frequency meets `y + ℤ` at most once, and a rational one never. -/
theorem lockPoint_orbit_inj {u : ℕ → ℝ} {y : ℝ} (hy : Irrational y) {p p' : ℕ × ℕ} {k k' : ℕ}
    (hp : lockPoint u p = y + k) (hp' : lockPoint u p' = y + k') (h : p.2 = p'.2) : p = p' := by
  by_cases hn : p.1 = p'.1
  · exact Prod.ext hn h
  · exfalso
    unfold lockPoint at hp hp'
    rw [← h] at hp'
    have hd : ((p.1 : ℝ) - p'.1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
    have hu' : u p.2 = ((k : ℝ) - k') / ((p.1 : ℝ) - p'.1) := by
      rw [eq_div_iff hd]; linarith
    apply hy
    refine ⟨(p.1 : ℚ) * (((k : ℚ) - k') / ((p.1 : ℚ) - p'.1)) - k, ?_⟩
    push_cast
    rw [← hu']
    linarith

/-- On a fibre `n u_j = t`, a pair is determined by its frequency index. -/
theorem lockPoint_fiber_inj {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) {t : ℝ} {p p' : ℕ × ℕ}
    (hp : lockPoint u p = t) (hp' : lockPoint u p' = t) (h : p.2 = p'.2) : p = p' := by
  unfold lockPoint at hp hp'
  rw [← h] at hp'
  have : (p.1 : ℝ) = p'.1 := mul_right_cancel₀ (hu p.2).ne' (hp.trans hp'.symm)
  exact Prod.ext (by exact_mod_cast this) h

/-- The fibre masses `S(t) = Σ_{n u_j = t} |c_j|` are summable. -/
theorem summable_fiber_norm {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖) (t : ℝ) :
    Summable fun p : ℕ × ℕ => if lockPoint u p = t then ‖c p.2‖ else 0 := by
  classical
  have hinj : Function.Injective (fun p : (lockPoint u ⁻¹' {t}) => p.1.2) := fun p q h =>
    Subtype.ext (lockPoint_fiber_inj hu p.2 q.2 h)
  have h1 := (summable_subtype_iff_indicator (f := fun p : ℕ × ℕ => ‖c p.2‖)
    (s := lockPoint u ⁻¹' {t})).mp (hc.comp_injective hinj)
  refine h1.congr fun p => ?_
  simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]

/-- **The orbit masses are summable.** For irrational `y`, `Σ_k S(y + k) ≤ Σ_j |c_j|`. -/
theorem summable_orbit_fiber_norm {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖) {y : ℝ} (hy : Irrational y) :
    Summable fun k : ℕ => ∑' p : ℕ × ℕ,
      if lockPoint u p = y + k then ‖c p.2‖ else 0 := by
  classical
  refine summable_of_sum_range_le (c := ∑' j, ‖c j‖)
    (fun k => tsum_nonneg fun p => by split_ifs; exacts [norm_nonneg _, le_rfl]) fun K => ?_
  set G : ℕ × ℕ → ℝ := fun p => ∑ k ∈ Finset.range K,
    if lockPoint u p = y + k then ‖c p.2‖ else 0 with hG
  have hGs : Summable G := summable_sum fun k _ => summable_fiber_norm hu hc _
  have hswap : ∑ k ∈ Finset.range K, ∑' p : ℕ × ℕ,
      (if lockPoint u p = y + k then ‖c p.2‖ else 0) = ∑' p, G p :=
    (Summable.tsum_finsetSum fun k _ => summable_fiber_norm hu hc _).symm
  rw [hswap]
  set A : Set (ℕ × ℕ) := {p | ∃ k : ℕ, lockPoint u p = y + k} with hA
  have hGle : ∀ p, G p ≤ ‖c p.2‖ := by
    intro p
    simp only [hG]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.filter (fun k : ℕ => lockPoint u p = y + k) (Finset.range K)).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => by
        have h1 := (Finset.mem_filter.mp ha).2
        have h2 := (Finset.mem_filter.mp hb).2
        have : (a : ℝ) = b := by linarith
        exact_mod_cast this
    calc ((Finset.filter (fun k : ℕ => lockPoint u p = y + k) (Finset.range K)).card : ℝ) *
          ‖c p.2‖ ≤ 1 * ‖c p.2‖ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (norm_nonneg _)
      _ = ‖c p.2‖ := one_mul _
  have hsupp : Function.support G ⊆ A := by
    intro p hp
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    by_contra hpA
    apply hk
    rw [if_neg]
    exact fun h => hpA ⟨k, h⟩
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine Summable.tsum_le_tsum_of_inj (fun p : A => p.1.2) (fun p q hpq => ?_)
    (fun j _ => norm_nonneg _) (fun p => hGle p.1) (hGs.subtype A) hc
  obtain ⟨k, hk⟩ := p.2
  obtain ⟨k', hk'⟩ := q.2
  exact Subtype.ext (lockPoint_orbit_inj hy hk hk' hpq)

/-- `|𝒫(t)| ≤ W √t S(t)` when `|a| ≤ W`. -/
theorem norm_lockPer_le {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖) {W : ℝ} (haW : ∀ n, ‖a n‖ ≤ W) {t : ℝ} (ht : 0 < t) :
    ‖lockPer a c u t‖ ≤ W * Real.sqrt t *
      ∑' p : ℕ × ℕ, if lockPoint u p = t then ‖c p.2‖ else 0 := by
  classical
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (haW 0)
  have hb : ∀ p : ℕ × ℕ, ‖(if lockPoint u p = t then lockWeight a c u p else 0)‖ ≤
      W * Real.sqrt t * (if lockPoint u p = t then ‖c p.2‖ else 0) := by
    intro p
    split_ifs with h
    · have hp0 : p.1 ≠ 0 := fun h0 => by
        unfold lockPoint at h; rw [h0, Nat.cast_zero, zero_mul] at h; linarith
      have hn : (1 : ℝ) ≤ p.1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp0
      have hut : u p.2 ≤ t := by
        unfold lockPoint at h
        nlinarith [hu p.2]
      unfold lockWeight
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      calc ‖a p.1‖ * ‖c p.2‖ * Real.sqrt (u p.2) ≤ W * ‖c p.2‖ * Real.sqrt t :=
            mul_le_mul (mul_le_mul_of_nonneg_right (haW _) (norm_nonneg _))
              (Real.sqrt_le_sqrt hut) (Real.sqrt_nonneg _) (mul_nonneg hW0 (norm_nonneg _))
        _ = W * Real.sqrt t * ‖c p.2‖ := by ring
    · rw [norm_zero, mul_zero]
  have hs := (summable_fiber_norm hu hc t).mul_left (W * Real.sqrt t)
  have hns := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  rw [lockPer_eq_tsum_ite, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hns).trans (hns.tsum_le_tsum hb hs)

/-- **Irrational lock points carry no weight.** If `|a| ≤ W`, `Σ_j |c_j| < ∞` and the period
function has period one, then `𝒫(y) = 0` for every irrational `y > 0`. -/
theorem lockPer_eq_zero_of_irrational {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖) {W : ℝ} (haW : ∀ n, ‖a n‖ ≤ W)
    (hper : ∀ x : ℝ, 0 < x → lockPer a c u (x + 1) = lockPer a c u x) {y : ℝ} (hy : Irrational y)
    (hy0 : 0 < y) : lockPer a c u y = 0 := by
  by_contra hne
  have hP : 0 < ‖lockPer a c u y‖ := norm_pos_iff.mpr hne
  have hS := summable_orbit_fiber_norm hu hc hy
  have hbound : ∀ k : ℕ, 1 / |(k : ℝ) + y| ^ (1 / 2 : ℝ) ≤
      (W / ‖lockPer a c u y‖) * ∑' p : ℕ × ℕ,
        (if lockPoint u p = y + k then ‖c p.2‖ else 0) := by
    intro k
    have hyk : 0 < y + k := by positivity
    have h1 := norm_lockPer_le hu hc haW hyk
    rw [lockPer_add_nat hper hy0 k] at h1
    have hsq : |(k : ℝ) + y| ^ (1 / 2 : ℝ) = Real.sqrt (y + k) := by
      rw [abs_of_pos (by linarith), Real.sqrt_eq_rpow, add_comm]
    have hsq0 : 0 < Real.sqrt (y + k) := Real.sqrt_pos.mpr hyk
    rw [hsq, div_mul_eq_mul_div, le_div_iff₀ hP, one_div, inv_mul_le_iff₀ hsq0]
    linarith
  have hsum : Summable fun k : ℕ => 1 / |(k : ℝ) + y| ^ (1 / 2 : ℝ) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hbound (hS.mul_left _)
  have := (Real.summable_one_div_nat_add_rpow y (1 / 2)).mp hsum
  norm_num at this

/-! ## The rational part of a lock -/

open Classical in
/-- The rational value of a rational real number, and `1` otherwise. -/
def realRat (x : ℝ) : ℚ := if h : ∃ q : ℚ, (q : ℝ) = x then h.choose else 1

theorem realRat_spec {x : ℝ} (h : ∃ q : ℚ, (q : ℝ) = x) : ((realRat x : ℚ) : ℝ) = x := by
  unfold realRat; rw [dif_pos h]; exact h.choose_spec

theorem realRat_of_not {x : ℝ} (h : ¬ ∃ q : ℚ, (q : ℝ) = x) : realRat x = 1 := by
  unfold realRat; rw [dif_neg h]

open Classical in
/-- The weight `√den 8^{ω(den)}` of a rational real number, and `1` otherwise. -/
def realDenWeight (x : ℝ) : ℝ := if ∃ q : ℚ, (q : ℝ) = x then denWeight (realRat x).den else 1

theorem one_le_realDenWeight (x : ℝ) : 1 ≤ realDenWeight x := by
  unfold realDenWeight
  split_ifs
  · exact one_le_denWeight (realRat x).den_nz
  · exact le_rfl

open Classical in
/-- The coefficients of the rational frequencies of a lock. -/
def ratPartCoeff (c : ℕ → ℂ) (u : ℕ → ℝ) (j : ℕ) : ℂ :=
  if ∃ q : ℚ, (q : ℝ) = u j then c j else 0

theorem ratPartFreq_pos {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) (j : ℕ) :
    0 < ((realRat (u j) : ℚ) : ℝ) := by
  by_cases h : ∃ q : ℚ, (q : ℝ) = u j
  · rw [realRat_spec h]; exact hu j
  · rw [realRat_of_not h]; norm_num

open Classical in
/-- **Only the rational lock points remain.** By the vanishing at irrational points, the
exponential coefficients of a lock are those of its rational part. -/
theorem lockExpCoeff_eq_ratPart {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) {W : ℝ} (haW : ∀ n, ‖a n‖ ≤ W)
    (hper : ∀ x : ℝ, 0 < x → lockPer a c u (x + 1) = lockPer a c u x) (n : ℕ) :
    lockExpCoeff a c u 1 n =
      lockExpCoeff a (ratPartCoeff c u) (fun j => ((realRat (u j) : ℚ) : ℝ)) 1 n := by
  have hc1 : Summable fun j => ‖c j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hc
  set r : ℕ → ℝ := fun j => ((realRat (u j) : ℚ) : ℝ) with hr
  set E : ℕ × ℕ → ℂ := fun p => cexp (2 * Real.pi * I * (((1 : ℝ) * lockPoint u p : ℝ) : ℂ) * n)
    with hE
  set I' : ℕ × ℕ → ℂ := fun p => if (0 < lockPoint u p ∧ lockPoint u p ≤ 1) ∧
    Irrational (lockPoint u p) then lockWeight a c u p * E p else 0 with hI
  have hW := summable_norm_lockWeight_le_one hu ha0 ha hc
  have hIs : Summable I' := Summable.of_norm_bounded hW fun p => by
    simp only [hI]
    split_ifs with h1 h2
    · rw [norm_mul, hE, norm_cexp_two_pi_I_mul, mul_one]
    · exact absurd h1.1 h2
    · rw [norm_zero]; exact norm_nonneg _
    · rw [norm_zero]
  /- The irrational part vanishes fibrewise. -/
  have hI0 : ∑' p, I' p = 0 := by
    have hfib := hIs.hasSum.tsum_fiberwise (lockPoint u)
    have hz : (fun t : ℝ => ∑' p : lockPoint u ⁻¹' {t}, I' p) = fun _ => 0 := by
      funext t
      by_cases ht : (0 < t ∧ t ≤ 1) ∧ Irrational t
      · have hval : ∀ p : lockPoint u ⁻¹' {t}, I' p =
            lockWeight a c u p * cexp (2 * Real.pi * I * (((1 : ℝ) * t : ℝ) : ℂ) * n) := by
          intro p
          have hp := p.2
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
          simp only [hI, hE, hp, if_pos ht]
        rw [tsum_congr hval, tsum_mul_right]
        have h0 : lockPer a c u t = 0 :=
          lockPer_eq_zero_of_irrational hu hc1 haW hper ht.2 ht.1.1
        unfold lockPer at h0
        rw [h0, zero_mul]
      · refine (tsum_congr fun p => ?_).trans tsum_zero
        have hp := p.2
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
        simp only [hI, hp, if_neg ht]
    rw [hz] at hfib
    exact (hfib.unique hasSum_zero)
  /- Termwise: the full term is the rational term plus the irrational term. -/
  have hterm : ∀ p : ℕ × ℕ,
      (if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then lockWeight a c u p * E p else 0) =
        (if 0 < lockPoint r p ∧ lockPoint r p ≤ 1 then lockWeight a (ratPartCoeff c u) r p *
          cexp (2 * Real.pi * I * (((1 : ℝ) * lockPoint r p : ℝ) : ℂ) * n) else 0) + I' p := by
    intro p
    simp only [hI, hE]
    rcases eq_or_ne p.1 0 with h0 | h0
    · have hy : lockPoint u p = 0 := by unfold lockPoint; rw [h0, Nat.cast_zero, zero_mul]
      have hy' : lockPoint r p = 0 := by unfold lockPoint; rw [h0, Nat.cast_zero, zero_mul]
      simp [hy, hy']
    by_cases hq : ∃ q : ℚ, (q : ℝ) = u p.2
    · have hrp : r p.2 = u p.2 := realRat_spec hq
      have hlp : lockPoint r p = lockPoint u p := by unfold lockPoint; rw [hrp]
      have hw : lockWeight a (ratPartCoeff c u) r p = lockWeight a c u p := by
        unfold lockWeight ratPartCoeff; rw [if_pos hq, hrp]
      have hrat : ¬ Irrational (lockPoint u p) := by
        obtain ⟨q, hq⟩ := hq
        intro hirr
        apply hirr
        refine ⟨(p.1 : ℚ) * q, ?_⟩
        unfold lockPoint; push_cast; rw [hq]
      rw [hlp, hw]
      split_ifs <;> simp_all
    · have hw : lockWeight a (ratPartCoeff c u) r p = 0 := by
        unfold lockWeight ratPartCoeff; rw [if_neg hq]; ring
      have hirr : Irrational (lockPoint u p) := by
        have hu' : Irrational (u p.2) := fun ⟨q, hq'⟩ => hq ⟨q, hq'⟩
        unfold lockPoint
        exact hu'.natCast_mul h0
      rw [hw]
      split_ifs <;> simp_all
  have hRs : Summable fun p : ℕ × ℕ =>
      (if 0 < lockPoint r p ∧ lockPoint r p ≤ 1 then lockWeight a (ratPartCoeff c u) r p *
        cexp (2 * Real.pi * I * (((1 : ℝ) * lockPoint r p : ℝ) : ℂ) * n) else 0) := by
    have hc' : Summable fun j => ‖ratPartCoeff c u j‖ * max 1 (r j)⁻¹ :=
      Summable.of_nonneg_of_le
        (fun j => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
        (fun j => by
          unfold ratPartCoeff
          split_ifs with hq
          · rw [show r j = u j from realRat_spec hq]
          · rw [norm_zero, zero_mul]
            exact mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _))) hc
    exact Summable.of_norm_bounded
      (summable_norm_lockWeight_le_one (fun j => ratPartFreq_pos hu j) ha0 ha hc') fun p => by
        split_ifs
        · rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]
        · rw [norm_zero]
  unfold lockExpCoeff
  rw [tsum_congr hterm, hRs.tsum_add hIs, hI0, add_zero]

/-! ## The theorem -/

/-- **Almost-periodic locks have limit-periodic coefficients.** Let `G` be a Herglotz producer for
the weights `lam` with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j c_j u_j^{−(s−½)}`, with
arbitrary positive real frequencies `u_j` and `Σ_j |c_j| max(1, u_j^{−1}) K(u_j) < ∞`, where
`K(u) = √den(u) 8^{ω(den u)}` for rational `u` and `K(u) = 1` otherwise. Then the coefficients of
`exp(Σ lam(n) n^{−s}/log n)` are `Σ_q Ψ_q(n)` with `Ψ_q` of period `q + 1`, `|Ψ_q| ≤ B_q` and
`Σ_q √(q+1) 8^{ω(q+1)} B_q < ∞`. -/
theorem almostPeriodicLock_limitPeriodic {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hcw : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹ * realDenWeight (u j))
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock c u (lineS τ) * G (lineS τ)) :
    ∃ (Ψ : (q : ℕ) → ZMod (q + 1) → ℂ) (B : ℕ → ℝ), (∀ q x, ‖Ψ q x‖ ≤ B q) ∧
      (Summable fun q : ℕ => Real.sqrt ((q : ℝ) + 1) * 8 ^ (q + 1).primeFactors.card * B q) ∧
      ∀ n : ℕ, n ≠ 0 → dirichletExp (lamLog lam) n = ∑' q, Ψ q n := by
  set a := dirichletExp (lamLog lam) with ha
  have hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹ :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
      (fun j => le_mul_of_one_le_right
        (mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
        (one_le_realDenWeight _)) hcw
  have ha0 : a 0 = 0 := dirichletExp_zero
  have ha32 : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    summable_norm_mul_rpow_dirichletExp hsl (σ := 3 / 2) (by norm_num)
  have hcoef : ∀ n : ℕ, n ≠ 0 → a n = lockExpCoeff a c u 1 n :=
    apLock_coefficients hsl hΦre hid hGc hGd hG2 hu hc hlock
  set W : ℝ := ∑' p : ℕ × ℕ, if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
    ‖lockWeight a c u p‖ else 0 with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun p => by split_ifs; exacts [norm_nonneg _, le_rfl]
  have haW : ∀ n, ‖a n‖ ≤ W := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [ha0, norm_zero]; exact hW0
    · rw [hcoef n hn]; exact norm_lockExpCoeff_le hu ha0 ha32 hc 1 n
  have hper : ∀ x : ℝ, 0 < x → lockPer a c u (x + 1) = lockPer a c u x := fun x hx =>
    lockPer_add_one hsl hΦre hid hGc hGd hG2 hu hc hlock hx
  set c' := ratPartCoeff c u with hc'def
  set r : ℕ → ℚ := fun j => realRat (u j) with hr
  have hu' : ∀ j, 0 < ((r j : ℚ) : ℝ) := fun j => ratPartFreq_pos hu j
  have hc' : Summable fun j => ‖c' j‖ * max 1 ((r j : ℝ))⁻¹ :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
      (fun j => by
        simp only [hc'def, hr, ratPartCoeff]
        split_ifs with hq
        · rw [realRat_spec hq]
        · rw [norm_zero, zero_mul]
          exact mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _))) hc
  have hcw' : Summable fun j => ‖c' j‖ * max 1 ((r j : ℝ))⁻¹ * denWeight (r j).den :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
        (denWeight_nonneg _))
      (fun j => by
        simp only [hc'def, hr, ratPartCoeff, realDenWeight]
        split_ifs with hq
        · rw [realRat_spec hq]
        · rw [norm_zero, zero_mul, zero_mul]
          exact mul_nonneg (mul_nonneg (norm_nonneg _)
            (le_trans zero_le_one (le_max_left _ _))) zero_le_one) hcw
  have hred := lockExpCoeff_eq_ratPart hu ha0 ha32 hc haW hper
  exact ⟨ratLockPart a c' r, ratLockMass a c' r,
    fun q x => norm_ratLockPart_le hu' ha0 ha32 hc' q x,
    summable_ratLockMass_weight hu' ha0 ha32 hcw',
    fun n hn => (hcoef n hn).trans ((hred n).trans
      (lockExpCoeff_eq_tsum_ratLockPart hu' ha0 ha32 hc' n))⟩

/-- **Almost-periodic locks force the Riemann hypothesis.** Let `G` be a Herglotz producer for the
weights `lam` with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j c_j u_j^{−(s−½)}`, with
arbitrary positive real frequencies `u_j`. Suppose
`Σ_j |c_j| max(1, u_j^{−1}) K(u_j) < ∞`, where `K(u) = √den(u) 8^{ω(den u)}` for rational `u` and
`K(u) = 1` otherwise. Then the Riemann hypothesis holds. -/
theorem almostPeriodicLock_riemannHypothesis {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hcw : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹ * realDenWeight (u j))
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock c u (lineS τ) * G (lineS τ)) :
    RiemannHypothesis := by
  obtain ⟨Ψ, B, hB, hW, hΨ⟩ :=
    almostPeriodicLock_limitPeriodic hsl hΦre hid hGc hGd hG2 hu hcw hlock
  exact limitPeriodic_producer_riemannHypothesis hsl hΦd hid hGc hGd hG2 hB hW hΨ

end

end AbelianTwist

end RHTower
