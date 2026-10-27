import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations

/-!
# The Ramanujan twins survive exactly on per-order relations

The torsion orbit `O_n` of primitive `n`-th roots of unity has the Ramanujan mode
`c_n(k) = Σ_{ζ ∈ O_n} ζ^k`, a real, `n`-periodic sequence. Over a common period `q`:

* **Orthogonality** (`sum_ramanujanSum_mul`, `sum_ramanujanMode_mul`):
  `Σ_{k<q} c_m(k) c_n(k) = q φ(n)` if `m = n` and `0` otherwise, because `Σ_{k<q} (ζη)^k` counts
  the pairs with `η = ζ⁻¹`, and `ζ⁻¹` is a primitive root of the same order as `ζ`.
* **Exact relations** (`ramanujanRelations_iff`). For modes `c_{ord α}` placed at nodes `α`,
  `Σ_α C_α c_{ord α} ≡ 0` iff the coefficients sum to zero over each order.
* **The twin law** (`ramanujanTwin_survivalCone_eq`). Every renormalization of the Ramanujan twin
  germ has survival cone exactly `{C : Σ_{ord α = m} C_α = 0 for every m}`.
* **Pure torsion** (`ramanujan_survivalCone_eq_zero_of_injective`). With one node per order the
  survival cone is `{0}`: in the periodic-germ framework this is the prime-place no-go, and its
  cause is the orthogonality of the Ramanujan modes.

So the matched cancellation for a torsion orbit of order `n ≥ 2` is available only against a twin
carrying the same mode `c_n`; a twin with any other modes leaves nothing.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open ArithmeticEffectivityTheory

/-! ### Reality and orthogonality of Ramanujan sums -/

/-- Ramanujan sums are real. -/
theorem ramanujanSum_im (n m : ℕ) : (ramanujanSum n m).im = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ramanujanSum]
  · rw [ramanujanSum_eq_sum_moebius hn m, Complex.im_sum]
    refine sum_eq_zero fun x _ => ?_
    split_ifs <;> simp

theorem ramanujanSum_eq_ofReal (n m : ℕ) : ramanujanSum n m = (ramanujanMode n m : ℂ) := by
  apply Complex.ext
  · simp [ramanujanMode]
  · simp [ramanujanMode, ramanujanSum_im]

/-- A geometric sum over a full period of a root of unity. -/
theorem sum_range_pow_of_pow_eq_one {w : ℂ} {q : ℕ} (hw : w ^ q = 1) :
    ∑ k ∈ range q, w ^ k = if w = 1 then (q : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · have h1 := geom_sum_mul w q
    rw [hw, sub_self] at h1
    exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr h)

/-- **Orthogonality of Ramanujan sums** over a common period. -/
theorem sum_ramanujanSum_mul {m n q : ℕ} (hm : 0 < m) (hn : 0 < n) (hmq : m ∣ q) (hnq : n ∣ q) :
    ∑ k ∈ range q, ramanujanSum m k * ramanujanSum n k =
      if m = n then (q : ℂ) * Nat.totient n else 0 := by
  simp only [ramanujanSum, sum_mul_sum, ← mul_pow]
  rw [sum_comm]
  simp_rw [sum_comm (s := range q)]
  have hpow : ∀ ζ ∈ primitiveRoots m ℂ, ∀ η ∈ primitiveRoots n ℂ, (ζ * η) ^ q = 1 := by
    intro ζ hζ η hη
    have hζ' := (mem_primitiveRoots hm).mp hζ
    have hη' := (mem_primitiveRoots hn).mp hη
    rw [mul_pow, (hζ'.pow_eq_one_iff_dvd q).mpr hmq, (hη'.pow_eq_one_iff_dvd q).mpr hnq, one_mul]
  rw [sum_congr rfl fun ζ hζ => sum_congr rfl fun η hη =>
    sum_range_pow_of_pow_eq_one (hpow ζ hζ η hη)]
  split_ifs with hmn
  · subst hmn
    -- For each `ζ` exactly one `η = ζ⁻¹` contributes.
    have hinner : ∀ ζ ∈ primitiveRoots m ℂ,
        ∑ η ∈ primitiveRoots m ℂ, (if ζ * η = 1 then (q : ℂ) else 0) = q := by
      intro ζ hζ
      have hζ' := (mem_primitiveRoots hm).mp hζ
      have hζ0 : ζ ≠ 0 := hζ'.ne_zero hm.ne'
      rw [sum_eq_single ζ⁻¹]
      · rw [if_pos (mul_inv_cancel₀ hζ0)]
      · intro η _ hne
        rw [if_neg]
        intro h
        exact hne (eq_inv_of_mul_eq_one_right h)
      · intro hnot
        exact absurd ((mem_primitiveRoots hm).mpr hζ'.inv) hnot
    rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul,
      (Complex.isPrimitiveRoot_exp m hm.ne').card_primitiveRoots]
    ring
  · refine sum_eq_zero fun ζ hζ => sum_eq_zero fun η hη => ?_
    rw [if_neg]
    intro h
    have hζ' := (mem_primitiveRoots hm).mp hζ
    have hη' := (mem_primitiveRoots hn).mp hη
    have hinv : η = ζ⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hinv] at hη'
    exact hmn (hζ'.inv.unique hη')

/-- Orthogonality of the real Ramanujan modes. -/
theorem sum_ramanujanMode_mul {m n q : ℕ} (hm : 0 < m) (hn : 0 < n) (hmq : m ∣ q) (hnq : n ∣ q) :
    ∑ k ∈ range q, ramanujanMode m k * ramanujanMode n k =
      if m = n then (q : ℝ) * Nat.totient n else 0 := by
  have h := congrArg Complex.re (sum_ramanujanSum_mul hm hn hmq hnq)
  simp only [ramanujanSum_eq_ofReal, ← Complex.ofReal_mul, Complex.re_sum,
    Complex.ofReal_re] at h
  rw [h]
  split_ifs <;> simp

/-! ### The twin germ -/

variable {N : ℕ}

/-- The common period of the orders. -/
abbrev twinPeriod (ord : Fin N → ℕ) : ℕ := ∏ γ, ord γ

theorem dvd_twinPeriod (ord : Fin N → ℕ) (α : Fin N) : ord α ∣ twinPeriod ord :=
  dvd_prod_of_mem _ (mem_univ α)

/-- **Exact relations among Ramanujan modes**: a combination vanishes identically iff the
coefficients sum to zero over each order. -/
theorem ramanujanRelations_iff (ord : Fin N → ℕ) (hord : ∀ α, 0 < ord α) (C : Fin N → ℝ) :
    (∀ k, ∑ α, C α * ramanujanMode (ord α) k = 0) ↔
      ∀ m : ℕ, ∑ α ∈ univ.filter (fun α => ord α = m), C α = 0 := by
  classical
  constructor
  · intro h m
    by_cases hm : ∃ β, ord β = m
    · obtain ⟨β, rfl⟩ := hm
      -- Pair the relation with the mode of order `ord β` over one common period.
      set q := twinPeriod ord
      have hpair : ∑ k ∈ range q, (∑ α, C α * ramanujanMode (ord α) k) *
          ramanujanMode (ord β) k = 0 := sum_eq_zero fun k _ => by rw [h k, zero_mul]
      have hexp : ∑ k ∈ range q, (∑ α, C α * ramanujanMode (ord α) k) *
          ramanujanMode (ord β) k =
            (q : ℝ) * Nat.totient (ord β) * ∑ α ∈ univ.filter (fun α => ord α = ord β), C α := by
        have hinner : ∀ α, ∑ k ∈ range q, C α * ramanujanMode (ord α) k *
            ramanujanMode (ord β) k =
              C α * (if ord α = ord β then (q : ℝ) * Nat.totient (ord β) else 0) := by
          intro α
          rw [← sum_ramanujanMode_mul (hord α) (hord β) (dvd_twinPeriod ord α)
            (dvd_twinPeriod ord β), mul_sum]
          exact sum_congr rfl fun k _ => by ring
        simp only [sum_mul]
        rw [sum_comm, sum_congr rfl fun α _ => hinner α, mul_sum, sum_filter]
        refine sum_congr rfl fun α _ => ?_
        split_ifs <;> ring
      rw [hexp] at hpair
      have hq : (0 : ℝ) < q := by exact_mod_cast prod_pos fun γ _ => hord γ
      have hφ : (0 : ℝ) < Nat.totient (ord β) := by exact_mod_cast Nat.totient_pos.mpr (hord β)
      exact (mul_eq_zero.mp hpair).resolve_left (mul_pos hq hφ).ne'
    · push Not at hm
      exact sum_eq_zero fun α hα => absurd (mem_filter.mp hα).2 (hm α)
  · intro hC k
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image ord) (g := ord)
      (fun α _ => mem_image_of_mem ord (mem_univ α))]
    refine sum_eq_zero fun m _ => ?_
    have hfib : ∑ α ∈ univ.filter (fun α => ord α = m), C α * ramanujanMode (ord α) k =
        (∑ α ∈ univ.filter (fun α => ord α = m), C α) * ramanujanMode m k := by
      rw [sum_mul]
      refine sum_congr rfl fun α hα => ?_
      rw [(mem_filter.mp hα).2]
    rw [hfib, hC m, zero_mul]

/-- The twin's modes are periodic over the common period. -/
theorem ramanujanMode_twinPeriodic (ord : Fin N → ℕ) (hord : ∀ α, 0 < ord α) (α : Fin N) :
    Function.Periodic (ramanujanMode (ord α)) (twinPeriod ord) := by
  have h := (ramanujanMode_periodic (hord α)).nat_mul (twinPeriod ord / ord α)
  rwa [Nat.cast_id, Nat.div_mul_cancel (dvd_twinPeriod ord α)] at h

/-- The Cesàro Gram of the twin is nonzero as soon as there is a node. -/
theorem cesaroGram_twin_ne_zero (ord : Fin N → ℕ) (hord : ∀ α, 0 < ord α) (hN : 0 < N) :
    cesaroGram (fun α => ramanujanMode (ord α)) (twinPeriod ord) ≠ 0 := by
  intro h
  have h0 := congrFun (congrFun h ⟨0, hN⟩) ⟨0, hN⟩
  simp only [cesaroGram, Matrix.of_apply, periodMean, Matrix.zero_apply] at h0
  rw [sum_ramanujanMode_mul (hord _) (hord _) (dvd_twinPeriod ord _) (dvd_twinPeriod ord _),
    if_pos rfl] at h0
  have hq : (0 : ℝ) < twinPeriod ord := by exact_mod_cast prod_pos fun γ _ => hord γ
  have hφ : (0 : ℝ) < Nat.totient (ord ⟨0, hN⟩) := by
    exact_mod_cast Nat.totient_pos.mpr (hord _)
  rw [mul_div_cancel_left₀ _ hq.ne'] at h0
  exact hφ.ne' h0

/-- **The twin law.** Every renormalization of the Ramanujan twin germ has survival cone exactly
the per-order relations. -/
theorem ramanujanTwin_survivalCone_eq (ord : Fin N → ℕ) (hord : ∀ α, 0 < ord α) (hN : 0 < N)
    {x : Fin N → ℝ} (hx : ∀ α, 0 ≤ x α) {t : ℝ → ℝ} {C' A' : Matrix (Fin N) (Fin N) ℝ}
    (hC : ∀ α β, Tendsto (fun r => periodicGerm (fun α => ramanujanMode (ord α)) x r α β -
      t r * C' α β) (𝓝[<] 1) (𝓝 (A' α β))) :
    survivalCone C' = {C | ∀ m : ℕ, ∑ α ∈ univ.filter (fun α => ord α = m), C α = 0} := by
  have hq : 0 < twinPeriod ord := prod_pos fun γ _ => hord γ
  rw [periodicGerm_survivalCone_eq _ hq (ramanujanMode_twinPeriodic ord hord) hx
    (cesaroGram_twin_ne_zero ord hord hN) hC]
  ext C
  exact ramanujanRelations_iff ord hord C

/-- **Pure torsion keeps nothing.** With one node per order the survival cone is `{0}`. -/
theorem ramanujan_survivalCone_eq_zero_of_injective (ord : Fin N → ℕ) (hord : ∀ α, 0 < ord α)
    (hinj : Function.Injective ord) (hN : 0 < N) {x : Fin N → ℝ} (hx : ∀ α, 0 ≤ x α)
    {t : ℝ → ℝ} {C' A' : Matrix (Fin N) (Fin N) ℝ}
    (hC : ∀ α β, Tendsto (fun r => periodicGerm (fun α => ramanujanMode (ord α)) x r α β -
      t r * C' α β) (𝓝[<] 1) (𝓝 (A' α β))) :
    survivalCone C' = {0} := by
  classical
  rw [ramanujanTwin_survivalCone_eq ord hord hN hx hC]
  ext C
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext α
    have h1 := h (ord α)
    rwa [show univ.filter (fun β => ord β = ord α) = {α} from by
      ext β; simp [hinj.eq_iff], sum_singleton] at h1
  · rintro rfl m
    simp

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
