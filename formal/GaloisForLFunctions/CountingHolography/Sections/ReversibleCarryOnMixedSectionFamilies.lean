import GaloisForLFunctions.CountingHolography.Sections.SubquadraticFibresOfMidpointSectionMaps
import GaloisForLFunctions.CountingHolography.Sections.SmallSectionsOnTheIntegerMomentKernel

/-!
# Reversible two-output carry rules and mixed-family section prototypes

This module resolves the positive half of the midpoint precision-export problem:

1. **Centered Euclidean carry involution and exact logarithmic window:**
   For `K : ℕ` and odd modulus `M = 2K + 1`, the integral coordinate map
   `centeredCarry K (z₁, z₂) = (balRem K z₁ + M z₂, balQuot K z₁)` is an exact
   involution on `ℤ × ℤ` satisfying `w₁ + M w₂ = z₁ + M z₂`. It maps
   `[-r₀, r₀]²` into `[-r₊, r₊] × [-r₋, r₋]` if and only if
   `r₀ ≤ M r₋ + K` and `M r₀ + K ≤ r₊` (whenever `K ≤ r₀`). Along a shifted
   ray `(m(kb - a), mkb, m(kb + a))` over a positive background `b`, an odd
   schedule `M_m = 2 K_m + 1` with `log M_m / m² → μ` embeds
   `S(mkb)² ↪ S(m(kb + a)) × S(m(kb - a))` eventually whenever
   `Q(kb) - Q(kb - a) < μ < Q(kb + a) - Q(kb)`, while cofinal validity forces
   `Q(kb) - Q(kb - a) ≤ μ ≤ Q(kb + a) - Q(kb)` and hence `0 ≤ Q(a)`.

2. **Parameter-free one-place block carry and mixed-family prototype:**
   Splitting `2^9 = 512` blocks recursively into `2^15 × 2^3 = 32768 × 8` blocks
   and conjugating by the signed bijection `ℤ ≃ ℕ` defines a single global
   parameter-free bijection `intBlockCarry : ℤ × ℤ ≃ ℤ × ℤ` specified purely by
   integral arithmetic before computing any section cardinalities. It preserves
   base-`2` block congruences (`mod 512^t ↔ mod 32768^t × mod 8^t`, exporting
   `6t` bits per block to the wide output) and maps `S(m v₀)²` injectively and
   reversibly into `S(m v₁) × S(m v₂)` whenever `5 Q(v₀) < 3 Q(v₁)` and
   `Q(v₀) < 3 Q(v₂)`. Combining integer moment kernels with Hecke dilation
   isometry (`integerProbe_dilate`) produces at every separation ratio `p ≥ 2`
   and unbounded horizons `p N` a positive background `b = U + V` and a
   genuinely mixed zero-sum displacement `a = 3U - V` with separated active
   conductors on which the single fixed bijection `intBlockCarry` restricts to a
   reversible section injection `S(3mb)² ↪ S(m(3b + a)) × S(m(3b - a))` for all
   sufficiently large `m`.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticScatteringHolography

/-- Symmetric half-length of the integer small-section interval of `v`. -/
def sectionRadius {N : ℕ} (v : Fin N → ℤ) : ℕ :=
  ⌊Real.exp (radius v) / (generator v : ℝ)⌋₊

theorem divisorSections_eq_Icc {N : ℕ} (v : Fin N → ℤ) :
    divisorSections v = Finset.Icc (-(sectionRadius v : ℤ)) (sectionRadius v) :=
  rfl

theorem card_divisorSections_eq {N : ℕ} (v : Fin N → ℤ) :
    (divisorSections v).card = 2 * sectionRadius v + 1 :=
  card_smallSections _ _

theorem tendsto_log_sectionRadius {N : ℕ} {v : Fin N → ℤ} (hv : 0 < integerProbe N v) :
    Tendsto (fun m : ℕ => Real.log (sectionRadius (m • v)) / (m : ℝ)^2) atTop
      (𝓝 (integerProbe N v)) := by
  have hcard : Tendsto (fun m : ℕ => logCard (m • v) / (m : ℝ)^2) atTop (𝓝 (integerProbe N v)) := by
    simpa only [max_eq_left hv.le] using logCard_tateLimit v
  have hzero (c : ℝ) : Tendsto (fun m : ℕ => c / (m : ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hge1 : ∀ᶠ m : ℕ in atTop, 1 ≤ sectionRadius (m • v) := by
    filter_upwards [(hzero (Real.log 3)).eventually_lt_const (half_pos hv),
      hcard.eventually_const_lt (half_lt_self hv), eventually_ge_atTop 1] with m hc hm hm1
    have hlt := hc.trans hm
    rw [div_lt_div_iff_of_pos_right (by positivity : 0 < (m : ℝ)^2)] at hlt
    unfold logCard at hlt
    have hc_pos : 0 < ((divisorSections (m • v)).card : ℝ) := by
      rw [card_divisorSections_eq]; positivity
    have h3 : (3 : ℝ) < (divisorSections (m • v)).card :=
      (Real.log_lt_log_iff (by norm_num) hc_pos).mp hlt
    have h3' : 3 < 2 * sectionRadius (m • v) + 1 := by
      rw [← card_divisorSections_eq]; exact_mod_cast h3
    omega
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hcard.sub (hzero (Real.log 3))) hcard ?_ ?_
  · filter_upwards [hge1] with m hr1
    rw [← sub_div]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have hr_pos : 0 < (sectionRadius (m • v) : ℝ) := by exact_mod_cast hr1
    have hle : ((divisorSections (m • v)).card : ℝ) ≤ 3 * (sectionRadius (m • v) : ℝ) := by
      rw [card_divisorSections_eq]; push_cast
      have : (1 : ℝ) ≤ sectionRadius (m • v) := by exact_mod_cast hr1
      linarith
    have hc_pos : 0 < ((divisorSections (m • v)).card : ℝ) := by
      rw [card_divisorSections_eq]; positivity
    have hlog := Real.log_le_log hc_pos hle
    rw [Real.log_mul (by norm_num) hr_pos.ne'] at hlog
    unfold logCard
    linarith only [hlog]
  · filter_upwards [hge1] with m hr1
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have hr_pos : 0 < (sectionRadius (m • v) : ℝ) := by exact_mod_cast hr1
    have hle : (sectionRadius (m • v) : ℝ) ≤ (divisorSections (m • v)).card := by
      rw [card_divisorSections_eq]; push_cast; linarith
    exact Real.log_le_log hr_pos hle

/-! ### 1. Centered Euclidean carry involution and exact logarithmic carry window -/

/-- Centered Euclidean quotient on `ℤ` at odd modulus `2K + 1`. -/
def balQuot (K : ℕ) (z : ℤ) : ℤ := (z + K) / (2 * (K : ℤ) + 1)

/-- Centered Euclidean remainder in `[-K, K]` at odd modulus `2K + 1`. -/
def balRem (K : ℕ) (z : ℤ) : ℤ := (z + K) % (2 * (K : ℤ) + 1) - K

private theorem ediv_emod_unique {M q r' : ℤ} (hM : 0 < M) (hr0 : 0 ≤ r') (hrM : r' < M) :
    (r' + M * q) / M = q ∧ (r' + M * q) % M = r' := by
  let A := r' + M * q
  have hdiv : M * (A / M) + A % M = A := Int.mul_ediv_add_emod A M
  have hm0 : 0 ≤ A % M := Int.emod_nonneg A hM.ne'
  have hmM : A % M < M := Int.emod_lt_of_pos A hM
  have hdiff : M * (A / M - q) = r' - A % M := by dsimp [A] at hdiv; linarith only [hdiv]
  have hq : A / M = q := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : A / M - q ≤ -1 := by omega
      nlinarith only [hM, hr0, hmM, hdiff, hle]
    · have hge : 1 ≤ A / M - q := by omega
      nlinarith only [hM, hrM, hm0, hdiff, hge]
  exact ⟨hq, by rw [hq] at hdiff; linarith only [hdiff]⟩

theorem balRem_bounds (K : ℕ) (z : ℤ) :
    -(K : ℤ) ≤ balRem K z ∧ balRem K z ≤ K := by
  have hM : 0 < 2 * (K : ℤ) + 1 := by omega
  have h0 := Int.emod_nonneg (z + K) hM.ne'
  have h1 := Int.emod_lt_of_pos (z + K) hM
  unfold balRem
  omega

theorem balRem_add_mul_balQuot (K : ℕ) (z : ℤ) :
    balRem K z + (2 * (K : ℤ) + 1) * balQuot K z = z := by
  unfold balRem balQuot
  have h := Int.mul_ediv_add_emod (z + K) (2 * (K : ℤ) + 1)
  linarith only [h]

/-- Centered Euclidean carry involution on `ℤ × ℤ` at odd modulus `2K + 1`. -/
def centeredCarry (K : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (balRem K p.1 + (2 * (K : ℤ) + 1) * p.2, balQuot K p.1)

/-- `centeredCarry K` is an exact involution on `ℤ × ℤ`. -/
theorem centeredCarry_involutive (K : ℕ) : Function.Involutive (centeredCarry K) := by
  rintro ⟨z₁, z₂⟩
  let M : ℤ := 2 * (K : ℤ) + 1
  have hM : 0 < M := by dsimp [M]; omega
  obtain ⟨hr_lo, hr_hi⟩ := balRem_bounds K z₁
  have huniq := ediv_emod_unique (q := z₂) (r' := balRem K z₁ + K) hM
    (by omega) (by dsimp [M]; omega)
  have heq : balRem K z₁ + M * z₂ + K = (balRem K z₁ + K) + M * z₂ := by ring
  have hq : balQuot K (balRem K z₁ + M * z₂) = z₂ := by
    unfold balQuot; change (balRem K z₁ + M * z₂ + K) / M = z₂
    rw [heq]; exact huniq.1
  have hr : balRem K (balRem K z₁ + M * z₂) = balRem K z₁ := by
    unfold balRem; change (balRem K z₁ + M * z₂ + K) % M - K = balRem K z₁
    rw [heq, huniq.2]; ring
  simp only [centeredCarry, Prod.mk.injEq]
  exact ⟨by dsimp [M] at hr ⊢; rw [hr]; exact balRem_add_mul_balQuot K z₁, hq⟩

theorem centeredCarry_bijective (K : ℕ) : Function.Bijective (centeredCarry K) :=
  (centeredCarry_involutive K).bijective

/-- Exact base-`(2K + 1)` linear conservation law for `centeredCarry K`. -/
theorem centeredCarry_linear_conservation (K : ℕ) (p : ℤ × ℤ) :
    (centeredCarry K p).1 + (2 * (K : ℤ) + 1) * (centeredCarry K p).2 =
      p.1 + (2 * (K : ℤ) + 1) * p.2 := by
  dsimp only [centeredCarry]
  linarith only [balRem_add_mul_balQuot K p.1]

/-- Sufficient condition for `centeredCarry K` to map `[-r₀, r₀]²` into `[-r₁, r₁] × [-r₂, r₂]`. -/
theorem centeredCarry_maps_Icc_of_bounds {K r₀ r₁ r₂ : ℕ}
    (h₂ : r₀ ≤ (2 * K + 1) * r₂ + K) (h₁ : (2 * K + 1) * r₀ + K ≤ r₁)
    {z₁ z₂ : ℤ} (hz₁ : z₁ ∈ Finset.Icc (-(r₀ : ℤ)) r₀) (hz₂ : z₂ ∈ Finset.Icc (-(r₀ : ℤ)) r₀) :
    (centeredCarry K (z₁, z₂)).1 ∈ Finset.Icc (-(r₁ : ℤ)) r₁ ∧
      (centeredCarry K (z₁, z₂)).2 ∈ Finset.Icc (-(r₂ : ℤ)) r₂ := by
  rw [Finset.mem_Icc] at hz₁ hz₂ ⊢
  rw [Finset.mem_Icc]
  obtain ⟨hr_lo, hr_hi⟩ := balRem_bounds K z₁
  have hdecomp := balRem_add_mul_balQuot K z₁
  let M : ℤ := 2 * (K : ℤ) + 1
  have hM : 0 < M := by dsimp [M]; omega
  have h₂' : (r₀ : ℤ) ≤ M * r₂ + K := by dsimp [M]; exact_mod_cast h₂
  have h₁' : M * (r₀ : ℤ) + K ≤ r₁ := by dsimp [M]; exact_mod_cast h₁
  refine ⟨?_, ?_⟩
  · dsimp only [centeredCarry]
    have hmul_lo : -M * (r₀ : ℤ) ≤ M * z₂ := by nlinarith only [hM, hz₂.1]
    have hmul_hi : M * z₂ ≤ M * (r₀ : ℤ) := by nlinarith only [hM, hz₂.2]
    exact ⟨by dsimp [M] at hmul_lo h₁'; linarith only [hr_lo, hmul_lo, h₁'],
           by dsimp [M] at hmul_hi h₁'; linarith only [hr_hi, hmul_hi, h₁']⟩
  · dsimp only [centeredCarry]
    change -(r₂ : ℤ) ≤ balQuot K z₁ ∧ balQuot K z₁ ≤ r₂
    have hq_eq : M * balQuot K z₁ = z₁ - balRem K z₁ := by
      dsimp [M]; linarith only [hdecomp]
    have hlo : -M * ((r₂ : ℤ) + 1) < M * balQuot K z₁ := by
      rw [hq_eq]; dsimp [M] at h₂' ⊢; linarith only [hz₁.1, hr_hi, h₂']
    have hhi : M * balQuot K z₁ < M * ((r₂ : ℤ) + 1) := by
      rw [hq_eq]; dsimp [M] at h₂' ⊢; linarith only [hz₁.2, hr_lo, h₂']
    have q_gt : -((r₂ : ℤ) + 1) < balQuot K z₁ := by
      by_contra! hle; nlinarith only [hM, hlo, hle]
    have q_lt : balQuot K z₁ < (r₂ : ℤ) + 1 := by
      by_contra! hge; nlinarith only [hM, hhi, hge]
    omega

/-- Necessary bounds whenever `centeredCarry K` maps `[-r₀, r₀]²` into `[-r₁, r₁] × [-r₂, r₂]`. -/
theorem bounds_of_centeredCarry_maps_Icc {K r₀ r₁ r₂ : ℕ}
    (h : ∀ z₁ ∈ Finset.Icc (-(r₀ : ℤ)) r₀, ∀ z₂ ∈ Finset.Icc (-(r₀ : ℤ)) r₀,
      (centeredCarry K (z₁, z₂)).1 ∈ Finset.Icc (-(r₁ : ℤ)) r₁ ∧
        (centeredCarry K (z₁, z₂)).2 ∈ Finset.Icc (-(r₂ : ℤ)) r₂) :
    r₀ ≤ (2 * K + 1) * r₂ + K ∧ (2 * K + 1) * r₀ + min K r₀ ≤ r₁ := by
  let u : ℤ := min (K : ℤ) r₀
  have hu_mem : u ∈ Finset.Icc (-(r₀ : ℤ)) r₀ := by
    rw [Finset.mem_Icc]
    exact ⟨by dsimp [u]; omega, min_le_right _ _⟩
  have hr0_mem : (r₀ : ℤ) ∈ Finset.Icc (-(r₀ : ℤ)) r₀ := by rw [Finset.mem_Icc]; omega
  have h0_mem : (0 : ℤ) ∈ Finset.Icc (-(r₀ : ℤ)) r₀ := by rw [Finset.mem_Icc]; omega
  have h1 := (Finset.mem_Icc.mp (h u hu_mem r₀ hr0_mem).1).2
  have hu_rem : balRem K u = u := by
    have huniq := ediv_emod_unique (M := 2 * (K : ℤ) + 1) (q := 0) (r' := u + K)
      (by omega) (by dsimp [u]; omega) (by dsimp [u]; omega)
    unfold balRem
    rw [show u + (K : ℤ) = (u + K) + (2 * (K : ℤ) + 1) * 0 by ring, huniq.2]
    ring
  dsimp only [centeredCarry] at h1
  rw [hu_rem] at h1
  have h2 := (Finset.mem_Icc.mp (h r₀ hr0_mem 0 h0_mem).2).2
  dsimp only [centeredCarry] at h2
  have hdecomp := balRem_add_mul_balQuot K r₀
  have hr_hi := (balRem_bounds K r₀).2
  have hmul : (2 * (K : ℤ) + 1) * balQuot K r₀ ≤ (2 * (K : ℤ) + 1) * r₂ :=
    Int.mul_le_mul_of_nonneg_left h2 (by omega)
  have h₂' : (r₀ : ℤ) ≤ (2 * (K : ℤ) + 1) * r₂ + K := by linarith only [hdecomp, hr_hi, hmul]
  have h₁' : (2 * (K : ℤ) + 1) * r₀ + min (K : ℤ) r₀ ≤ r₁ := by dsimp [u] at h1; linarith only [h1]
  exact ⟨by exact_mod_cast h₂', by exact_mod_cast h₁'⟩

/-- Exact necessary-and-sufficient interval condition for `centeredCarry K` when `K ≤ r₀`. -/
theorem centeredCarry_maps_Icc_iff {K r₀ r₁ r₂ : ℕ} (hKr : K ≤ r₀) :
    (∀ z₁ ∈ Finset.Icc (-(r₀ : ℤ)) r₀, ∀ z₂ ∈ Finset.Icc (-(r₀ : ℤ)) r₀,
      (centeredCarry K (z₁, z₂)).1 ∈ Finset.Icc (-(r₁ : ℤ)) r₁ ∧
        (centeredCarry K (z₁, z₂)).2 ∈ Finset.Icc (-(r₂ : ℤ)) r₂) ↔
      r₀ ≤ (2 * K + 1) * r₂ + K ∧ (2 * K + 1) * r₀ + K ≤ r₁ := by
  constructor
  · intro h
    obtain ⟨h₂, h₁⟩ := bounds_of_centeredCarry_maps_Icc h
    rw [min_eq_left hKr] at h₁
    exact ⟨h₂, h₁⟩
  · rintro ⟨h₂, h₁⟩ z₁ hz₁ z₂ hz₂
    exact centeredCarry_maps_Icc_of_bounds h₂ h₁ hz₁ hz₂

/-- Any odd carry schedule `M_m = 2 K_m + 1` whose normalized logarithmic scale `μ`
lies strictly inside `(Q(v₀) - Q(v₂), Q(v₁) - Q(v₀))` eventually restricts to a
reversible midpoint section injection `S(m v₀)² ↪ S(m v₁) × S(m v₂)`. -/
theorem eventually_centeredCarry_sections_of_window {N : ℕ} {v₀ v₁ v₂ : Fin N → ℤ}
    (hv₀ : 0 < integerProbe N v₀) (hv₁ : 0 < integerProbe N v₁) (hv₂ : 0 < integerProbe N v₂)
    {K : ℕ → ℕ} {μ : ℝ}
    (hK : Tendsto (fun m : ℕ => Real.log (2 * K m + 1 : ℕ) / (m : ℝ)^2) atTop (𝓝 μ))
    (hlo : integerProbe N v₀ - integerProbe N v₂ < μ)
    (hhi : μ < integerProbe N v₁ - integerProbe N v₀) :
    ∀ᶠ m : ℕ in atTop, mapsDivisorSections (centeredCarry (K m)) (m • v₀) (m • v₁) (m • v₂) := by
  have hr₀ := tendsto_log_sectionRadius hv₀
  have hr₁ := tendsto_log_sectionRadius hv₁
  have hr₂ := tendsto_log_sectionRadius hv₂
  have hc2 : Tendsto (fun m : ℕ => Real.log 2 / (m : ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hev₂ := ((hK.add hr₂).sub hr₀).eventually_const_lt
    (show (0 : ℝ) < μ + integerProbe N v₂ - integerProbe N v₀ by linarith)
  have hev₁ := (((hr₁.sub hK).sub hr₀).sub hc2).eventually_const_lt
    (show (0 : ℝ) < integerProbe N v₁ - μ - integerProbe N v₀ - 0 by linarith)
  have hpos {v : Fin N → ℤ} (hv : 0 < integerProbe N v) :
      ∀ᶠ m : ℕ in atTop, 1 ≤ sectionRadius (m • v) := by
    filter_upwards [(tendsto_log_sectionRadius hv).eventually_const_lt (half_lt_self hv),
      eventually_ge_atTop 1] with m hm hm1
    by_contra! h0
    have hz : sectionRadius (m • v) = 0 := by omega
    rw [hz, Nat.cast_zero, Real.log_zero, zero_div] at hm
    linarith [half_pos hv]
  filter_upwards [hev₂, hev₁, hpos hv₀, hpos hv₂, hpos hv₁, eventually_ge_atTop 1]
    with m hm₂ hm₁ h₀ h₂ h₁ hm1
  intro z₁ hz₁ z₂ hz₂
  rw [divisorSections_eq_Icc] at hz₁ hz₂ ⊢
  rw [divisorSections_eq_Icc]
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  let M : ℕ := 2 * K m + 1
  have hM : 0 < M := by dsimp [M]; omega
  refine centeredCarry_maps_Icc_of_bounds ?_ ?_ hz₁ hz₂
  · have hd : 0 < (Real.log (M : ℝ) + Real.log (sectionRadius (m • v₂)) -
        Real.log (sectionRadius (m • v₀))) / (m : ℝ)^2 := by
      simpa only [M, add_div, sub_div] using hm₂
    have hlog := (lt_div_iff₀ hm2).mp hd
    rw [zero_mul] at hlog
    have hlt : Real.log (sectionRadius (m • v₀)) <
        Real.log ((M * sectionRadius (m • v₂) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr hM).ne' (Nat.cast_pos.mpr h₂).ne']
      linarith only [hlog]
    have hnat : sectionRadius (m • v₀) < M * sectionRadius (m • v₂) := by
      exact_mod_cast (Real.log_lt_log_iff (Nat.cast_pos.mpr h₀)
        (Nat.cast_pos.mpr (Nat.mul_pos hM h₂))).mp hlt
    dsimp [M] at hnat; omega
  · have hd : 0 < (Real.log (sectionRadius (m • v₁)) - Real.log (M : ℝ) -
        Real.log (sectionRadius (m • v₀)) - Real.log 2) / (m : ℝ)^2 := by
      simpa only [M, sub_div] using hm₁
    have hlog := (lt_div_iff₀ hm2).mp hd
    rw [zero_mul] at hlog
    have hlt : Real.log ((2 * M * sectionRadius (m • v₀) : ℕ) : ℝ) <
        Real.log (sectionRadius (m • v₁)) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat,
        Real.log_mul (mul_ne_zero two_ne_zero (Nat.cast_pos.mpr hM).ne') (Nat.cast_pos.mpr h₀).ne',
        Real.log_mul two_ne_zero (Nat.cast_pos.mpr hM).ne']
      linarith only [hlog]
    have hnat : 2 * M * sectionRadius (m • v₀) < sectionRadius (m • v₁) := by
      exact_mod_cast (Real.log_lt_log_iff
        (Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos (by decide) hM) h₀))
        (Nat.cast_pos.mpr h₁)).mp hlt
    have hK_le : K m ≤ M * sectionRadius (m • v₀) := by
      have : K m ≤ M * 1 := by dsimp [M]; omega
      exact this.trans (Nat.mul_le_mul_left M h₀)
    change M * sectionRadius (m • v₀) + K m ≤ sectionRadius (m • v₁)
    linarith only [hnat, hK_le]

/-- Conversely, if `centeredCarry (K m)` maps `S(m(kb))²` into `S(m(kb + a)) × S(m(kb - a))`
cofinally often for any schedule `K` at cofinal translations `k` of a positive
background `b`, then `0 ≤ Q(a)`. -/
theorem integerProbe_nonneg_of_cofinal_centeredCarry {N : ℕ} (b a : Fin N → ℤ)
    (hb : 0 < integerProbe N b)
    (h : ∃ᶠ k : ℕ in atTop, ∃ᶠ m : ℕ in atTop, ∃ K : ℕ,
      mapsDivisorSections (centeredCarry K) (m • (k • b)) (m • (k • b + a)) (m • (k • b - a))) :
    0 ≤ integerProbe N a := by
  refine integerProbe_nonneg_of_subquadraticMidpointFibres b a hb (h.mono fun k hk => ?_)
  refine hasSubquadraticMidpointFibres_of_frequently_embeds (hk.mono fun m ⟨K, hK⟩ => ?_)
  refine ⟨⟨restrictSectionMap (centeredCarry K) hK, fun p q hpq => ?_⟩⟩
  simp only [restrictSectionMap, Prod.ext_iff, Subtype.ext_iff] at hpq
  have hinj := (centeredCarry_bijective K).injective (Prod.ext hpq.1 hpq.2)
  exact Prod.ext (Subtype.ext (Prod.ext_iff.mp hinj).1) (Subtype.ext (Prod.ext_iff.mp hinj).2)

/-! ### 2. Parameter-free base-2 block carry bijection on `ℤ × ℤ` -/

/-- Recursive parameter-free base-`2` block carry on `ℕ × ℕ`, splitting each
`512 × 512` input digit pair into a `32768 × 8` output digit pair. -/
def natBlockCarry (x₁ x₂ : ℕ) : ℕ × ℕ :=
  if x₁ = 0 ∧ x₂ = 0 then (0, 0)
  else
    let r := natBlockCarry (x₁ / 512) (x₂ / 512)
    (((x₁ % 512) / 8 + 64 * (x₂ % 512)) + 32768 * r.1,
     (x₁ % 512) % 8 + 8 * r.2)
termination_by x₁ + x₂
decreasing_by omega

/-- Explicit arithmetic inverse of `natBlockCarry`. -/
def natBlockRecover (y₁ y₂ : ℕ) : ℕ × ℕ :=
  if y₁ = 0 ∧ y₂ = 0 then (0, 0)
  else
    let r := natBlockRecover (y₁ / 32768) (y₂ / 8)
    (((y₂ % 8) + 8 * ((y₁ % 32768) % 64)) + 512 * r.1,
     (y₁ % 32768) / 64 + 512 * r.2)
termination_by y₁ + y₂
decreasing_by omega

theorem natBlockCarry_step (x₁ x₂ : ℕ) :
    natBlockCarry x₁ x₂ =
      let r := natBlockCarry (x₁ / 512) (x₂ / 512)
      (((x₁ % 512) / 8 + 64 * (x₂ % 512)) + 32768 * r.1,
       (x₁ % 512) % 8 + 8 * r.2) := by
  rw [natBlockCarry]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    have h0 : natBlockCarry 0 0 = (0, 0) := by rw [natBlockCarry]; simp
    simp [h0]
  · rfl

theorem natBlockRecover_step (y₁ y₂ : ℕ) :
    natBlockRecover y₁ y₂ =
      let r := natBlockRecover (y₁ / 32768) (y₂ / 8)
      (((y₂ % 8) + 8 * ((y₁ % 32768) % 64)) + 512 * r.1,
       (y₁ % 32768) / 64 + 512 * r.2) := by
  rw [natBlockRecover]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    have h0 : natBlockRecover 0 0 = (0, 0) := by rw [natBlockRecover]; simp
    simp [h0]
  · rfl

theorem natBlockRecover_carry (x₁ x₂ : ℕ) :
    natBlockRecover (natBlockCarry x₁ x₂).1 (natBlockCarry x₁ x₂).2 = (x₁, x₂) := by
  by_cases h0 : x₁ = 0 ∧ x₂ = 0
  · rcases h0 with ⟨rfl, rfl⟩
    have hc : natBlockCarry 0 0 = (0, 0) := by rw [natBlockCarry]; simp
    have hr : natBlockRecover 0 0 = (0, 0) := by rw [natBlockRecover]; simp
    simp [hc, hr]
  · rw [natBlockCarry_step, natBlockRecover_step]
    let r := natBlockCarry (x₁ / 512) (x₂ / 512)
    let c := (x₁ % 512) / 8 + 64 * (x₂ % 512)
    have hc_lt : c < 32768 := by dsimp [c]; omega
    have hd1 : (c + 32768 * r.1) / 32768 = r.1 := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 32768), Nat.div_eq_of_lt hc_lt, zero_add]
    have hm1 : (c + 32768 * r.1) % 32768 = c := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc_lt]
    have hd2 : ((x₁ % 512) % 8 + 8 * r.2) / 8 = r.2 := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 8), Nat.div_eq_of_lt (by omega), zero_add]
    have hm2 : ((x₁ % 512) % 8 + 8 * r.2) % 8 = (x₁ % 512) % 8 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    dsimp only
    change (let s := natBlockRecover ((c + 32768 * r.1) / 32768) (((x₁ % 512) % 8 + 8 * r.2) / 8);
      ((((x₁ % 512) % 8 + 8 * r.2) % 8 + 8 * (((c + 32768 * r.1) % 32768) % 64)) + 512 * s.1,
       ((c + 32768 * r.1) % 32768) / 64 + 512 * s.2)) = (x₁, x₂)
    rw [hd1, hm1, hd2, hm2]
    have ih : natBlockRecover r.1 r.2 = (x₁ / 512, x₂ / 512) :=
      natBlockRecover_carry (x₁ / 512) (x₂ / 512)
    dsimp only [r] at ih
    rw [show r = natBlockCarry (x₁ / 512) (x₂ / 512) from rfl, ih]
    dsimp only [c]
    ext <;> dsimp only <;> omega
termination_by x₁ + x₂
decreasing_by omega

theorem natBlockCarry_recover (y₁ y₂ : ℕ) :
    natBlockCarry (natBlockRecover y₁ y₂).1 (natBlockRecover y₁ y₂).2 = (y₁, y₂) := by
  by_cases h0 : y₁ = 0 ∧ y₂ = 0
  · rcases h0 with ⟨rfl, rfl⟩
    have hr : natBlockRecover 0 0 = (0, 0) := by rw [natBlockRecover]; simp
    have hc : natBlockCarry 0 0 = (0, 0) := by rw [natBlockCarry]; simp
    simp [hr, hc]
  · rw [natBlockRecover_step, natBlockCarry_step]
    let r := natBlockRecover (y₁ / 32768) (y₂ / 8)
    let a := (y₂ % 8) + 8 * ((y₁ % 32768) % 64)
    let b := (y₁ % 32768) / 64
    have ha_lt : a < 512 := by dsimp [a]; omega
    have hb_lt : b < 512 := by dsimp [b]; omega
    have hd1 : (a + 512 * r.1) / 512 = r.1 := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 512), Nat.div_eq_of_lt ha_lt, zero_add]
    have hm1 : (a + 512 * r.1) % 512 = a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha_lt]
    have hd2 : (b + 512 * r.2) / 512 = r.2 := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 512), Nat.div_eq_of_lt hb_lt, zero_add]
    have hm2 : (b + 512 * r.2) % 512 = b := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb_lt]
    dsimp only
    change (let s := natBlockCarry ((a + 512 * r.1) / 512) ((b + 512 * r.2) / 512);
      ((((a + 512 * r.1) % 512) / 8 + 64 * ((b + 512 * r.2) % 512)) + 32768 * s.1,
       ((a + 512 * r.1) % 512) % 8 + 8 * s.2)) = (y₁, y₂)
    rw [hd1, hm1, hd2, hm2]
    have ih : natBlockCarry r.1 r.2 = (y₁ / 32768, y₂ / 8) :=
      natBlockCarry_recover (y₁ / 32768) (y₂ / 8)
    dsimp only [r] at ih
    rw [show r = natBlockRecover (y₁ / 32768) (y₂ / 8) from rfl, ih]
    dsimp only [a, b]
    ext <;> dsimp only <;> omega
termination_by y₁ + y₂
decreasing_by omega

/-- Explicit parameter-free bijection `ℕ × ℕ ≃ ℕ × ℕ` given by base-`2` block carry. -/
def natBlockCarryEquiv : ℕ × ℕ ≃ ℕ × ℕ where
  toFun p := natBlockCarry p.1 p.2
  invFun q := natBlockRecover q.1 q.2
  left_inv p := natBlockRecover_carry p.1 p.2
  right_inv q := natBlockCarry_recover q.1 q.2

/-- Exact base-`2` block congruence preservation: `natBlockCarry` sends
congruence modulo `512^t` in both inputs to congruence modulo `32768^t × 8^t`
in the two outputs, exporting `6t` bits per block to the first output. -/
theorem natBlockCarry_modEq (t : ℕ) {x₁ x₂ x₁' x₂' : ℕ}
    (h₁ : x₁ ≡ x₁' [MOD 512 ^ t]) (h₂ : x₂ ≡ x₂' [MOD 512 ^ t]) :
    (natBlockCarry x₁ x₂).1 ≡ (natBlockCarry x₁' x₂').1 [MOD 32768 ^ t] ∧
      (natBlockCarry x₁ x₂).2 ≡ (natBlockCarry x₁' x₂').2 [MOD 8 ^ t] := by
  induction t generalizing x₁ x₂ x₁' x₂' with
  | zero => simp [Nat.ModEq, Nat.mod_one]
  | succ t ih =>
    have hpow : 512 ^ (t + 1) = 512 * 512 ^ t := by rw [pow_succ, mul_comm]
    rw [hpow] at h₁ h₂
    have hm₁ : x₁ % 512 = x₁' % 512 := h₁.of_dvd (dvd_mul_right 512 (512 ^ t))
    have hm₂ : x₂ % 512 = x₂' % 512 := h₂.of_dvd (dvd_mul_right 512 (512 ^ t))
    have hdiv_mod {u v : ℕ} (huv : u ≡ v [MOD 512 * 512 ^ t]) (hm : u % 512 = v % 512) :
        u / 512 ≡ v / 512 [MOD 512 ^ t] := by
      have hmul : 512 * (u / 512) ≡ 512 * (v / 512) [MOD 512 * 512 ^ t] := by
        apply Nat.ModEq.add_left_cancel' (u % 512)
        have hu := Nat.mod_add_div u 512
        have hv := Nat.mod_add_div v 512
        rwa [hu, hm, hv]
      change (u / 512) % 512 ^ t = (v / 512) % 512 ^ t
      have heq : (512 * (u / 512)) % (512 * 512 ^ t) = (512 * (v / 512)) % (512 * 512 ^ t) := hmul
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at heq
      exact Nat.mul_left_cancel (by decide : 0 < 512) heq
    obtain ⟨ih₁, ih₂⟩ := ih (hdiv_mod h₁ hm₁) (hdiv_mod h₂ hm₂)
    rw [natBlockCarry_step x₁ x₂, natBlockCarry_step x₁' x₂']
    dsimp only
    rw [hm₁, hm₂]
    have hmul₁ : 32768 * (natBlockCarry (x₁ / 512) (x₂ / 512)).1 ≡
        32768 * (natBlockCarry (x₁' / 512) (x₂' / 512)).1 [MOD 32768 ^ (t + 1)] := by
      rw [show 32768 ^ (t + 1) = 32768 * 32768 ^ t by rw [pow_succ, mul_comm]]
      change (32768 * _) % (32768 * 32768 ^ t) = (32768 * _) % (32768 * 32768 ^ t)
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
      exact congrArg (32768 * ·) ih₁
    have hmul₂ : 8 * (natBlockCarry (x₁ / 512) (x₂ / 512)).2 ≡
        8 * (natBlockCarry (x₁' / 512) (x₂' / 512)).2 [MOD 8 ^ (t + 1)] := by
      rw [show 8 ^ (t + 1) = 8 * 8 ^ t by rw [pow_succ, mul_comm]]
      change (8 * _) % (8 * 8 ^ t) = (8 * _) % (8 * 8 ^ t)
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
      exact congrArg (8 * ·) ih₂
    exact ⟨Nat.ModEq.add_left _ hmul₁, Nat.ModEq.add_left _ hmul₂⟩

theorem natBlockCarry_lt_pow (t : ℕ) {x₁ x₂ : ℕ}
    (h₁ : x₁ < 512 ^ t) (h₂ : x₂ < 512 ^ t) :
    (natBlockCarry x₁ x₂).1 < 32768 ^ t ∧ (natBlockCarry x₁ x₂).2 < 8 ^ t := by
  induction t generalizing x₁ x₂ with
  | zero =>
    have hx₁ : x₁ = 0 := by omega
    have hx₂ : x₂ = 0 := by omega
    subst hx₁ hx₂
    have h0 : natBlockCarry 0 0 = (0, 0) := by rw [natBlockCarry]; simp
    simp [h0]
  | succ t ih =>
    have hdiv₁ : x₁ / 512 < 512 ^ t :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 512)).mpr (by rwa [pow_succ] at h₁)
    have hdiv₂ : x₂ / 512 < 512 ^ t :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 512)).mpr (by rwa [pow_succ] at h₂)
    obtain ⟨ih₁, ih₂⟩ := ih hdiv₁ hdiv₂
    rw [natBlockCarry_step]
    dsimp only
    have hc : (x₁ % 512) / 8 + 64 * (x₂ % 512) < 32768 := by omega
    have hd : (x₁ % 512) % 8 < 8 := by omega
    rw [pow_succ 32768 t, pow_succ 8 t]
    exact ⟨by linarith [Nat.mul_le_mul_left 32768 (Nat.succ_le_of_lt ih₁)],
           by linarith [Nat.mul_le_mul_left 8 (Nat.succ_le_of_lt ih₂)]⟩

theorem natBlockCarry_cube_bounds {x₁ x₂ B : ℕ} (hB : 1 ≤ B) (h₁ : x₁ ≤ B) (h₂ : x₂ ≤ B) :
    (natBlockCarry x₁ x₂).1 ^ 3 < 512 ^ 5 * B ^ 5 ∧
      (natBlockCarry x₁ x₂).2 ^ 3 < 512 * B := by
  let L := Nat.log 512 B
  have hpow_le : 512 ^ L ≤ B := Nat.pow_log_le_self 512 (by omega)
  have hB_lt : B < 512 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 512) B
  obtain ⟨hy₁, hy₂⟩ := natBlockCarry_lt_pow (L + 1) (h₁.trans_lt hB_lt) (h₂.trans_lt hB_lt)
  refine ⟨?_, ?_⟩
  · calc (natBlockCarry x₁ x₂).1 ^ 3
        < (32768 ^ (L + 1)) ^ 3 := Nat.pow_lt_pow_left hy₁ (by decide)
      _ = (32768 ^ 3) ^ (L + 1) := by rw [← pow_mul, mul_comm, pow_mul]
      _ = (512 ^ 5) ^ (L + 1) := by rw [show (32768 : ℕ) ^ 3 = 512 ^ 5 by decide]
      _ = 512 ^ 5 * (512 ^ L) ^ 5 := by rw [pow_succ, mul_comm, ← pow_mul, mul_comm 5 L, pow_mul]
      _ ≤ 512 ^ 5 * B ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow_le 5)
  · calc (natBlockCarry x₁ x₂).2 ^ 3
        < (8 ^ (L + 1)) ^ 3 := Nat.pow_lt_pow_left hy₂ (by decide)
      _ = (8 ^ 3) ^ (L + 1) := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 512 ^ (L + 1) := by rw [show (8 : ℕ) ^ 3 = 512 by decide]
      _ = 512 * 512 ^ L := by rw [pow_succ, mul_comm]
      _ ≤ 512 * B := Nat.mul_le_mul_left 512 hpow_le

/-- Signed zigzag encoding `ℤ → ℕ`. -/
def zigZag (z : ℤ) : ℕ :=
  if 0 ≤ z then (2 * z).toNat else (-2 * z - 1).toNat

/-- Inverse signed zigzag decoding `ℕ → ℤ`. -/
def unZigZag (n : ℕ) : ℤ :=
  if n % 2 = 0 then (n / 2 : ℕ) else -((n / 2 : ℕ) : ℤ) - 1

theorem zigZagEquiv_left_inv (z : ℤ) : unZigZag (zigZag z) = z := by
  unfold zigZag unZigZag
  split_ifs <;> omega

theorem zigZagEquiv_right_inv (n : ℕ) : zigZag (unZigZag n) = n := by
  unfold zigZag unZigZag
  split_ifs <;> omega

/-- Explicit arithmetic bijection `ℤ ≃ ℕ`. -/
def zigZagEquiv : ℤ ≃ ℕ where
  toFun := zigZag
  invFun := unZigZag
  left_inv := zigZagEquiv_left_inv
  right_inv := zigZagEquiv_right_inv

/-- Single parameter-free global carry bijection `ℤ × ℤ ≃ ℤ × ℤ`, specified
purely by integral arithmetic independently of any divisor or multiplicity. -/
def intBlockCarry : ℤ × ℤ ≃ ℤ × ℤ :=
  (zigZagEquiv.prodCongr zigZagEquiv).trans
    (natBlockCarryEquiv.trans (zigZagEquiv.symm.prodCongr zigZagEquiv.symm))

theorem intBlockCarry_maps_Icc_of_cube_bounds {r₀ r₁ r₂ : ℕ} (hr₀ : 1 ≤ r₀)
    (h₁ : 32 * 512 ^ 5 * r₀ ^ 5 ≤ r₁ ^ 3) (h₂ : 1024 * r₀ ≤ r₂ ^ 3)
    {z₁ z₂ : ℤ} (hz₁ : z₁ ∈ Finset.Icc (-(r₀ : ℤ)) r₀) (hz₂ : z₂ ∈ Finset.Icc (-(r₀ : ℤ)) r₀) :
    (intBlockCarry (z₁, z₂)).1 ∈ Finset.Icc (-(r₁ : ℤ)) r₁ ∧
      (intBlockCarry (z₁, z₂)).2 ∈ Finset.Icc (-(r₂ : ℤ)) r₂ := by
  rw [Finset.mem_Icc] at hz₁ hz₂ ⊢
  rw [Finset.mem_Icc]
  have hx₁ : zigZag z₁ ≤ 2 * r₀ := by unfold zigZag; split_ifs <;> omega
  have hx₂ : zigZag z₂ ≤ 2 * r₀ := by unfold zigZag; split_ifs <;> omega
  obtain ⟨hy₁, hy₂⟩ := natBlockCarry_cube_bounds (B := 2 * r₀) (by omega) hx₁ hx₂
  let y := natBlockCarry (zigZag z₁) (zigZag z₂)
  have hy₁_le : y.1 ≤ r₁ := by
    have hcube : y.1 ^ 3 < r₁ ^ 3 := by
      calc y.1 ^ 3 < 512 ^ 5 * (2 * r₀) ^ 5 := hy₁
        _ = 32 * 512 ^ 5 * r₀ ^ 5 := by ring
        _ ≤ r₁ ^ 3 := h₁
    by_contra! hgt
    exact hcube.not_ge (Nat.pow_le_pow_left hgt.le 3)
  have hy₂_le : y.2 ≤ r₂ := by
    have hcube : y.2 ^ 3 < r₂ ^ 3 := by
      calc y.2 ^ 3 < 512 * (2 * r₀) := hy₂
        _ = 1024 * r₀ := by ring
        _ ≤ r₂ ^ 3 := h₂
    by_contra! hgt
    exact hcube.not_ge (Nat.pow_le_pow_left hgt.le 3)
  have hunz (n b : ℕ) (hnb : n ≤ b) : -(b : ℤ) ≤ unZigZag n ∧ unZigZag n ≤ b := by
    unfold unZigZag; split_ifs <;> omega
  exact ⟨hunz y.1 r₁ hy₁_le, hunz y.2 r₂ hy₂_le⟩

/-- Whenever `0 < Q(v₀)`, `5 Q(v₀) < 3 Q(v₁)`, and `Q(v₀) < 3 Q(v₂)`, the single
parameter-free bijection `intBlockCarry` eventually maps `S(m v₀)²` into
`S(m v₁) × S(m v₂)` and restricts to an explicit reversible section injection. -/
theorem eventually_intBlockCarry_sections {N : ℕ} {v₀ v₁ v₂ : Fin N → ℤ}
    (hv₀ : 0 < integerProbe N v₀)
    (hv₁ : 5 * integerProbe N v₀ < 3 * integerProbe N v₁)
    (hv₂ : integerProbe N v₀ < 3 * integerProbe N v₂) :
    ∀ᶠ m : ℕ in atTop, mapsDivisorSections intBlockCarry (m • v₀) (m • v₁) (m • v₂) := by
  have hv₁_pos : 0 < integerProbe N v₁ := by linarith
  have hv₂_pos : 0 < integerProbe N v₂ := by linarith
  have hr₀ := tendsto_log_sectionRadius hv₀
  have hr₁ := tendsto_log_sectionRadius hv₁_pos
  have hr₂ := tendsto_log_sectionRadius hv₂_pos
  have hc (c : ℕ) : Tendsto (fun m : ℕ => Real.log (c : ℝ) / (m : ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hev₁ := (((hr₁.const_mul 3).sub (hr₀.const_mul 5)).sub (hc (32 * 512 ^ 5))).eventually_const_lt
    (show (0 : ℝ) < 3 * integerProbe N v₁ - 5 * integerProbe N v₀ - 0 by linarith)
  have hev₂ := (((hr₂.const_mul 3).sub hr₀).sub (hc 1024)).eventually_const_lt
    (show (0 : ℝ) < 3 * integerProbe N v₂ - integerProbe N v₀ - 0 by linarith)
  have hpos {v : Fin N → ℤ} (hv : 0 < integerProbe N v) :
      ∀ᶠ m : ℕ in atTop, 1 ≤ sectionRadius (m • v) := by
    filter_upwards [(tendsto_log_sectionRadius hv).eventually_const_lt (half_lt_self hv),
      eventually_ge_atTop 1] with m hm hm1
    by_contra! h0
    have hz : sectionRadius (m • v) = 0 := by omega
    rw [hz, Nat.cast_zero, Real.log_zero, zero_div] at hm
    linarith [half_pos hv]
  filter_upwards [hev₁, hev₂, hpos hv₀, hpos hv₁_pos, hpos hv₂_pos, eventually_ge_atTop 1]
    with m hm₁ hm₂ h₀ h₁ h₂ hm1
  intro z₁ hz₁ z₂ hz₂
  rw [divisorSections_eq_Icc] at hz₁ hz₂ ⊢
  rw [divisorSections_eq_Icc]
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  refine intBlockCarry_maps_Icc_of_cube_bounds h₀ ?_ ?_ hz₁ hz₂
  · have hd : 0 < (3 * Real.log (sectionRadius (m • v₁)) - 5 * Real.log (sectionRadius (m • v₀)) -
        Real.log ((32 * 512 ^ 5 : ℕ) : ℝ)) / (m : ℝ)^2 := by
      simpa only [sub_div, mul_div_assoc] using hm₁
    have hlog := (lt_div_iff₀ hm2).mp hd
    rw [zero_mul] at hlog
    have hlt : Real.log (((32 * 512 ^ 5) * sectionRadius (m • v₀) ^ 5 : ℕ) : ℝ) <
        Real.log ((sectionRadius (m • v₁) ^ 3 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by norm_num) (Nat.cast_pos.mpr (pow_pos h₀ 5)).ne',
        Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
      push_cast at hlog ⊢
      linarith only [hlog]
    exact ((Real.log_lt_log_iff (Nat.cast_pos.mpr (Nat.mul_pos (by decide) (pow_pos h₀ 5)))
      (Nat.cast_pos.mpr (pow_pos h₁ 3))).mp hlt).le |> fun h => by exact_mod_cast h
  · have hd : 0 < (3 * Real.log (sectionRadius (m • v₂)) - Real.log (sectionRadius (m • v₀)) -
        Real.log ((1024 : ℕ) : ℝ)) / (m : ℝ)^2 := by
      simpa only [sub_div, mul_div_assoc] using hm₂
    have hlog := (lt_div_iff₀ hm2).mp hd
    rw [zero_mul] at hlog
    have hlt : Real.log ((1024 * sectionRadius (m • v₀) : ℕ) : ℝ) <
        Real.log ((sectionRadius (m • v₂) ^ 3 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by norm_num) (Nat.cast_pos.mpr h₀).ne',
        Nat.cast_pow, Real.log_pow]
      push_cast at hlog ⊢
      linarith only [hlog]
    exact ((Real.log_lt_log_iff (Nat.cast_pos.mpr (Nat.mul_pos (by decide) h₀))
      (Nat.cast_pos.mpr (pow_pos h₂ 3))).mp hlt).le |> fun h => by exact_mod_cast h

/-- On any positive ray `b`, the single parameter-free bijection `intBlockCarry`
restricts for all sufficiently large `m` to an explicit reversible injection
`S(3mb)² ↪ S(4mb) × S(2mb)`. -/
theorem eventually_intBlockCarry_positive_ray {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, mapsDivisorSections intBlockCarry
      (m • (3 • b)) (m • (4 • b)) (m • (2 • b)) := by
  have h3 : integerProbe N (3 • b) = 9 * integerProbe N b := by rw [integerProbe_smul]; norm_num
  have h4 : integerProbe N (4 • b) = 16 * integerProbe N b := by rw [integerProbe_smul]; norm_num
  have h2 : integerProbe N (2 • b) = 4 * integerProbe N b := by rw [integerProbe_smul]; norm_num
  exact eventually_intBlockCarry_sections (by linarith) (by linarith) (by linarith)

/-! ### 3. Unconditional genuinely mixed family with separated conductors -/

private theorem sum_extend_zero {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {e : ι → κ} (he : Function.Injective e) (w : κ → ℝ) (u : ι → ℤ) :
    (∑ ℓ : κ, w ℓ * ((Function.extend e u 0 ℓ : ℤ) : ℝ)) = ∑ i : ι, w (e i) * (u i : ℝ) := by
  have hoff : ∀ ℓ, ℓ ∉ Finset.univ.image e →
      w ℓ * ((Function.extend e u 0 ℓ : ℤ) : ℝ) = 0 := by
    intro ℓ hℓ
    have hz : Function.extend e u 0 ℓ = 0 :=
      Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    rw [hz, Int.cast_zero, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) fun ℓ _ hℓ => hoff ℓ hℓ,
    Finset.sum_image fun i _ j _ h => he h]
  exact Finset.sum_congr rfl fun i _ => by rw [he.extend_apply]

private def halfWindowReadings (N k : ℕ) :
    (Fin N → ℚ) →ₗ[ℚ] ((Fin (N / 2) → ℚ) × (Fin k → ℚ)) where
  toFun v := (fun i => v (Fin.castLE (Nat.div_le_self N 2) i),
    fun j => ∑ i : Fin N, ((i : ℚ) + 1) ^ j.val * v i)
  map_add' v w := by
    apply Prod.ext
    · rfl
    funext j
    change ∑ i : Fin N, ((i : ℚ) + 1) ^ j.val * (v i + w i) =
      (∑ i : Fin N, ((i : ℚ) + 1) ^ j.val * v i) + ∑ i : Fin N, ((i : ℚ) + 1) ^ j.val * w i
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    apply Prod.ext
    · rfl
    funext j
    change ∑ i : Fin N, ((i : ℚ) + 1) ^ j.val * (c * v i) = c * ∑ i : Fin N, ((i : ℚ) + 1) ^ j.val * v i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- For every separation ratio `p ≥ 2`, there is a fixed moment threshold `N₀`
such that at every horizon `N ≥ N₀`, `ℤ^(p * N)` contains a positive background
`b` and a genuinely mixed zero-sum signed displacement `a = 3U - V` whose
positive-group (`U`) and negative-group (`V`) conductors are separated by factor
`> p / 2`, and on which the **single fixed parameter-free bijection**
`intBlockCarry : ℤ × ℤ ≃ ℤ × ℤ` restricts for all large `m` to an explicit
reversible injection `S(3mb)² ↪ S(m(3b + a)) × S(m(3b - a))`. -/
theorem exists_mixed_family_reversible_blockCarry (p : ℕ) (hp : 2 ≤ p) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ (U V b a : Fin (p * N) → ℤ),
        b = U + V ∧ a = 3 • U - V ∧
        (∀ ℓ, U ℓ = 0 ∨ V ℓ = 0) ∧
        (∀ i j : Fin (p * N), U i ≠ 0 → V j ≠ 0 → p * (i.val + 1) < 2 * (j.val + 1)) ∧
        (∑ ℓ, a ℓ) = 0 ∧ (∃ ℓ₁, 0 < a ℓ₁) ∧ (∃ ℓ₂, a ℓ₂ < 0) ∧
        0 < integerProbe (p * N) b ∧ 0 < integerProbe (p * N) a ∧
        (∀ᶠ m : ℕ in atTop,
          ∃ h : mapsDivisorSections intBlockCarry
            (m • (3 • b)) (m • (3 • b + a)) (m • (3 • b - a)),
            Function.Injective (restrictSectionMap intBlockCarry h) ∧
            ∀ x : ↥(divisorSections (m • (3 • b))) × ↥(divisorSections (m • (3 • b))),
              intBlockCarry.symm
                ((restrictSectionMap intBlockCarry h x).1.val,
                 (restrictSectionMap intBlockCarry h x).2.val) = (x.1.val, x.2.val)) := by
  have hp0 : 0 < p := by omega
  obtain ⟨k, hk_pos⟩ := positive_integer_window_moments (2 * p) (by omega)
  let k₀ := max k 1
  refine ⟨2 * k₀ + 2, fun N hN => ?_⟩
  let T := halfWindowReadings N k₀
  have hrank : 0 < Module.finrank ℚ (LinearMap.ker T) := by
    have he := T.finrank_range_add_finrank_ker
    have hl := Submodule.finrank_le (LinearMap.range T)
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he hl
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ : ∃ v ∈ LinearMap.ker T, v ≠ 0 := by
    by_contra! hall
    have hbot : LinearMap.ker T = ⊥ := (Submodule.eq_bot_iff _).mpr hall
    rw [hbot, finrank_bot] at hrank
    exact lt_irrefl 0 hrank
  obtain ⟨D, u, hD, hd⟩ := ArithmeticScatteringHolography.exists_common_denominator v
  have hu_eq : (fun i => (u i : ℚ)) = (D : ℚ) • v := by
    funext i; change (u i : ℚ) = (D : ℚ) * v i; rw [mul_comm]; exact_mod_cast (hd i).symm
  have hu_ne : u ≠ 0 := by
    intro h0
    apply hv_ne
    funext i
    have hi : (u i : ℚ) = (D : ℚ) * v i := congrFun hu_eq i
    rw [h0, Pi.zero_apply, Int.cast_zero] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left (Nat.cast_ne_zero.mpr hD.ne')
  have hu_ker : T (fun i => (u i : ℚ)) = 0 :=
    LinearMap.mem_ker.mp (hu_eq ▸ (LinearMap.ker T).smul_mem _ hv_mem)
  have hu_low (i : Fin N) (hi : i.val < N / 2) : u i = 0 := by
    have h := congrFun (congrArg Prod.fst hu_ker) ⟨i.val, hi⟩
    change (u i : ℚ) = 0 at h
    exact_mod_cast h
  have hu_mom (j : ℕ) (hj : j < k₀) : ∑ i : Fin N, ((i : ℝ) + 1) ^ j * (u i : ℝ) = 0 := by
    have h := congrFun (congrArg Prod.snd hu_ker) ⟨j, hj⟩
    change ∑ i : Fin N, ((i : ℚ) + 1) ^ j * (u i : ℚ) = 0 at h
    exact_mod_cast h
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by simpa [funext_iff] using hu_ne
  have hsum_u : (∑ i : Fin N, u i) = 0 := by
    have h0 := hu_mom 0 (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right k 1))
    simp only [pow_zero, one_mul] at h0
    exact_mod_cast h0
  obtain ⟨i₁, hi₁⟩ : ∃ i : Fin N, 0 < u i := by
    by_contra! hnonpos
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · have hsplit := Finset.add_sum_erase Finset.univ u (Finset.mem_univ i₀)
      have hrest : ∑ i ∈ Finset.univ.erase i₀, u i ≤ 0 :=
        Finset.sum_nonpos fun i _ => hnonpos i
      linarith only [hsplit, hsum_u, hrest, hneg]
    · exact (hnonpos i₀).not_gt hpos
  let hle : N ≤ p * N := Nat.le_mul_of_pos_left N hp0
  let ePad : Fin N → Fin (p * N) := fun i => ⟨i.val, i.isLt.trans_le hle⟩
  have hePad : Function.Injective ePad :=
    fun i j hij => Fin.ext (congrArg (Fin.val : Fin (p * N) → ℕ) hij)
  let U : Fin (p * N) → ℤ := padDivisor hle u
  let V : Fin (p * N) → ℤ := CountingHolography.dilate hp0 u
  let b : Fin (p * N) → ℤ := U + V
  let w : Fin (p * N) → ℤ := U - V
  let a : Fin (p * N) → ℤ := 3 • U - V
  have hU_supp {ℓ : Fin (p * N)} (hU : U ℓ ≠ 0) : N / 2 ≤ ℓ.val ∧ ℓ.val < N := by
    by_cases hex : ∃ i : Fin N, ePad i = ℓ
    · obtain ⟨i, rfl⟩ := hex
      have hUeq : U (ePad i) = u i := hePad.extend_apply u 0 i
      have hui : u i ≠ 0 := by rwa [hUeq] at hU
      refine ⟨?_, i.isLt⟩
      by_contra! hlt
      exact hui (hu_low i hlt)
    · exact (hU (Function.extend_apply' _ _ _ hex)).elim
  have hV_supp {ℓ : Fin (p * N)} (hV : V ℓ ≠ 0) : p * (N / 2 + 1) ≤ ℓ.val + 1 := by
    by_cases hex : ∃ i : Fin N, CountingHolography.dilateIndex hp0 N i = ℓ
    · obtain ⟨i, rfl⟩ := hex
      have hui : u i ≠ 0 := by
        simpa only [V, CountingHolography.dilate,
          (CountingHolography.dilateIndex_injective hp0 N).extend_apply] using hV
      have hi_ge : N / 2 ≤ i.val := by
        by_contra! hlt; exact hui (hu_low i hlt)
      have hval := CountingHolography.dilateIndex_val hp0 N i
      have hnat : (CountingHolography.dilateIndex hp0 N i).val + 1 = p * (i.val + 1) := by
        exact_mod_cast hval
      rw [hnat]
      exact Nat.mul_le_mul_left p (Nat.add_le_add_right hi_ge 1)
    · exact (hV (Function.extend_apply' _ _ _ hex)).elim
  have hsep (i j : Fin (p * N)) (hUi : U i ≠ 0) (hVj : V j ≠ 0) :
      p * (i.val + 1) < 2 * (j.val + 1) := by
    have hi_lt : i.val < N := (hU_supp hUi).2
    have hj_ge : p * (N / 2 + 1) ≤ j.val + 1 := hV_supp hVj
    have hN_le : N < 2 * (N / 2 + 1) := by omega
    calc p * (i.val + 1) ≤ p * N := Nat.mul_le_mul_left p hi_lt
      _ < p * (2 * (N / 2 + 1)) := Nat.mul_lt_mul_of_pos_left hN_le hp0
      _ = 2 * (p * (N / 2 + 1)) := by ring
      _ ≤ 2 * (j.val + 1) := Nat.mul_le_mul_left 2 hj_ge
  have hdisj (ℓ : Fin (p * N)) : U ℓ = 0 ∨ V ℓ = 0 := by
    by_contra! hboth
    have h1 := (hU_supp hboth.1).2
    have h2 := hV_supp hboth.2
    have : 2 * (N / 2 + 1) ≤ p * (N / 2 + 1) := Nat.mul_le_mul_right _ hp
    omega
  have hU_mom (j : ℕ) (hj : j < k₀) :
      ∑ ℓ : Fin (p * N), ((ℓ : ℝ) + 1) ^ j * (U ℓ : ℝ) = 0 := by
    rw [show U = Function.extend ePad u 0 from rfl,
      sum_extend_zero hePad (fun ℓ => ((ℓ : ℝ) + 1) ^ j) u]
    exact hu_mom j hj
  have hV_mom (j : ℕ) (hj : j < k₀) :
      ∑ ℓ : Fin (p * N), ((ℓ : ℝ) + 1) ^ j * (V ℓ : ℝ) = 0 := by
    rw [show V = Function.extend (CountingHolography.dilateIndex hp0 N) u 0 from rfl,
      sum_extend_zero (CountingHolography.dilateIndex_injective hp0 N)
        (fun ℓ => ((ℓ : ℝ) + 1) ^ j) u]
    have hpull : (∑ i : Fin N, (((CountingHolography.dilateIndex hp0 N i : ℕ) : ℝ) + 1) ^ j * (u i : ℝ)) =
        (p : ℝ) ^ j * ∑ i : Fin N, ((i : ℝ) + 1) ^ j * (u i : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [CountingHolography.dilateIndex_val, mul_pow, mul_assoc]
    rw [hpull, hu_mom j hj, mul_zero]
  have hcomb_pos (c₁ c₂ : ℤ) (hc₁ : c₁ ≠ 0) :
      0 < integerProbe (p * N) (c₁ • U + c₂ • V) := by
    refine hk_pos (p * N) (c₁ • U + c₂ • V) ?_ ?_ ?_
    · intro hzero
      have hval := congrFun hzero (ePad i₀)
      have hUi₀ : U (ePad i₀) = u i₀ := hePad.extend_apply u 0 i₀
      have hVi₀ : V (ePad i₀) = 0 :=
        (hdisj (ePad i₀)).resolve_left (by rw [hUi₀]; exact hi₀)
      change c₁ • U (ePad i₀) + c₂ • V (ePad i₀) = 0 at hval
      rw [zsmul_eq_mul, zsmul_eq_mul, hUi₀, hVi₀, mul_zero, add_zero] at hval
      exact mul_ne_zero hc₁ hi₀ hval
    · intro ℓ hℓ
      have hdiv_eq : p * N / (2 * p) = N / 2 := by
        rw [mul_comm 2 p]
        exact Nat.mul_div_mul_left N 2 hp0
      rw [hdiv_eq] at hℓ
      have hU0 : U ℓ = 0 := by by_contra hne; exact hℓ.not_ge (hU_supp hne).1
      have hV0 : V ℓ = 0 := by
        by_contra hne
        have hge := hV_supp hne
        have : 2 * (N / 2 + 1) ≤ p * (N / 2 + 1) := Nat.mul_le_mul_right _ hp
        omega
      simp [hU0, hV0]
    · intro j hj
      have hj' : j < k₀ := hj.trans_le (le_max_left k 1)
      have hexp : (∑ ℓ : Fin (p * N), ((ℓ : ℝ) + 1) ^ j * (((c₁ • U + c₂ • V) ℓ : ℤ) : ℝ)) =
          (c₁ : ℝ) * (∑ ℓ : Fin (p * N), ((ℓ : ℝ) + 1) ^ j * (U ℓ : ℝ)) +
            (c₂ : ℝ) * (∑ ℓ : Fin (p * N), ((ℓ : ℝ) + 1) ^ j * (V ℓ : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        change ((ℓ : ℝ) + 1) ^ j * ((c₁ • U ℓ + c₂ • V ℓ : ℤ) : ℝ) = _
        simp only [zsmul_eq_mul, Int.cast_add, Int.cast_mul]
        ring
      rw [hexp, hU_mom j hj', hV_mom j hj', mul_zero, mul_zero, add_zero]
  have hb_pos : 0 < integerProbe (p * N) b := by
    simpa only [b, one_smul] using hcomb_pos 1 1 one_ne_zero
  have hw_pos : 0 < integerProbe (p * N) w := by
    have h := hcomb_pos 1 (-1) one_ne_zero
    simpa only [w, one_smul, neg_one_smul, sub_eq_add_neg] using h
  have ha_pos : 0 < integerProbe (p * N) a := by
    have h := hcomb_pos 3 (-1) (by decide)
    have h3 : (3 : ℤ) • U = (3 : ℕ) • U := by ext ℓ; simp
    rw [h3] at h
    simpa only [a, neg_one_smul, sub_eq_add_neg] using h
  have ha_sum : (∑ ℓ : Fin (p * N), a ℓ) = 0 := by
    have h0U := hU_mom 0 (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right k 1))
    have h0V := hV_mom 0 (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right k 1))
    simp only [pow_zero, one_mul] at h0U h0V
    have hreal : (∑ ℓ : Fin (p * N), (a ℓ : ℝ)) = 0 := by
      have hexp : (∑ ℓ : Fin (p * N), (a ℓ : ℝ)) =
          3 * (∑ ℓ : Fin (p * N), (U ℓ : ℝ)) - ∑ ℓ : Fin (p * N), (V ℓ : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        change (((3 : ℕ) • U ℓ - V ℓ : ℤ) : ℝ) = _
        simp only [nsmul_eq_mul]
        push_cast
        ring
      rw [hexp, h0U, h0V]; ring
    exact_mod_cast hreal
  have ha_pos_entry : ∃ ℓ₁, 0 < a ℓ₁ := by
    refine ⟨ePad i₁, ?_⟩
    have hUi : U (ePad i₁) = u i₁ := hePad.extend_apply u 0 i₁
    have hVi : V (ePad i₁) = 0 :=
      (hdisj (ePad i₁)).resolve_left (by rw [hUi]; omega)
    change 0 < (3 : ℕ) • U (ePad i₁) - V (ePad i₁)
    rw [nsmul_eq_mul, hUi, hVi]
    omega
  have ha_neg_entry : ∃ ℓ₂, a ℓ₂ < 0 := by
    let ℓ₂ := CountingHolography.dilateIndex hp0 N i₁
    refine ⟨ℓ₂, ?_⟩
    have hVi : V ℓ₂ = u i₁ :=
      (CountingHolography.dilateIndex_injective hp0 N).extend_apply u 0 i₁
    have hUi : U ℓ₂ = 0 :=
      (hdisj ℓ₂).resolve_right (by rw [hVi]; omega)
    change (3 : ℕ) • U ℓ₂ - V ℓ₂ < 0
    rw [nsmul_eq_mul, hUi, hVi]
    omega
  -- Parallelogram calculation of `Q(3b + a)` and `Q(3b - a)` via Hecke dilation isometry.
  have hQUV : integerProbe (p * N) U = integerProbe (p * N) V := by
    dsimp only [U, V]
    rw [integerProbe_pad, CountingHolography.integerProbe_dilate]
  have hbw_add : b + w = 2 • U := by
    ext ℓ; change (U ℓ + V ℓ) + (U ℓ - V ℓ) = (2 : ℕ) • U ℓ; rw [nsmul_eq_mul]; ring
  have hbw_sub : b - w = 2 • V := by
    ext ℓ; change (U ℓ + V ℓ) - (U ℓ - V ℓ) = (2 : ℕ) • V ℓ; rw [nsmul_eq_mul]; ring
  have hQ_bw_eq : integerProbe (p * N) (b + w) = integerProbe (p * N) (b - w) := by
    rw [hbw_add, hbw_sub, integerProbe_smul, integerProbe_smul, hQUV]
  have hpar1 := integerProbe_parallelogram (p * N) b w
  have hQ_bw : integerProbe (p * N) (b - w) =
      integerProbe (p * N) b + integerProbe (p * N) w := by
    linarith only [hpar1, hQ_bw_eq]
  have hpar2 := integerProbe_parallelogram (p * N) (b + w) b
  have h2bw_add : b + w + b = 2 • b + w := by
    ext ℓ; change (b ℓ + w ℓ) + b ℓ = (2 : ℕ) • b ℓ + w ℓ; rw [nsmul_eq_mul]; ring
  have h2bw_sub : b + w - b = w := by ext ℓ; simp
  rw [h2bw_add, h2bw_sub, hQ_bw_eq, hQ_bw] at hpar2
  have h3b_plus : 3 • b + a = 2 • (2 • b + w) := by
    ext ℓ
    change (3 : ℕ) • (U ℓ + V ℓ) + ((3 : ℕ) • U ℓ - V ℓ) =
      (2 : ℕ) • ((2 : ℕ) • (U ℓ + V ℓ) + (U ℓ - V ℓ))
    simp only [nsmul_eq_mul]; ring
  have h3b_minus : 3 • b - a = 2 • (b - w) := by
    ext ℓ
    change (3 : ℕ) • (U ℓ + V ℓ) - ((3 : ℕ) • U ℓ - V ℓ) = (2 : ℕ) • (b ℓ - w ℓ)
    dsimp only [b, w, Pi.add_apply, Pi.sub_apply]
    simp only [nsmul_eq_mul]; ring
  have hQ_mid : integerProbe (p * N) (3 • b) = 9 * integerProbe (p * N) b := by
    rw [integerProbe_smul]; norm_num
  have hQ_out₁ : integerProbe (p * N) (3 • b + a) =
      16 * integerProbe (p * N) b + 4 * integerProbe (p * N) w := by
    rw [h3b_plus, integerProbe_smul]; push_cast; linarith only [hpar2]
  have hQ_out₂ : integerProbe (p * N) (3 • b - a) =
      4 * integerProbe (p * N) b + 4 * integerProbe (p * N) w := by
    rw [h3b_minus, integerProbe_smul, hQ_bw]; push_cast; ring
  have hev := eventually_intBlockCarry_sections (v₀ := 3 • b) (v₁ := 3 • b + a) (v₂ := 3 • b - a)
    (by linarith) (by linarith) (by linarith)
  refine ⟨U, V, b, a, rfl, rfl, hdisj, hsep, ha_sum, ha_pos_entry, ha_neg_entry,
    hb_pos, ha_pos, hev.mono fun m hm => ⟨hm, ?_, ?_⟩⟩
  · intro x y hxy
    simp only [restrictSectionMap, Prod.ext_iff, Subtype.ext_iff] at hxy
    have hinj := intBlockCarry.injective (Prod.ext hxy.1 hxy.2)
    exact Prod.ext (Subtype.ext (Prod.ext_iff.mp hinj).1) (Subtype.ext (Prod.ext_iff.mp hinj).2)
  · intro x
    exact intBlockCarry.symm_apply_apply (x.1.val, x.2.val)

end GaloisForLFunctions.CountingHolography.Sections
