import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.WindowRelation

/-!
# Height-window certificates for the RH multiplicity ladder

The ladder `RHLadder k` quantifies over all ξ-zeros of the half-plane `Re s > ½`; regional
localization collapses the quantifier to the half-open box `{½ < Re < 1, 0 ≤ Im}`.  This file cuts
that box into bounded height windows and develops the resulting compact-exhaustion theory: each
window carries a **finite certificate** (its ξ-zeros form a finite set, and the certificate is the
divisibility of their finitely many vanishing orders), the certificates are monotone in height and
level, and they exhaust the ladder — `RHLadder k` is the conjunction of the height-`T` certificates
over all `T`, and RH itself is decided by the diagonal sequence of certificates.  Each certificate
is in turn equivalent to the existence of an analytic `2^k`-th root of ξ on a bounded truncated
half-band, giving a per-window Kummer correspondence, and to a family of dyadic congruences on the
reflection-closed sub-configurations of the window's actual zero divisor, giving the boundary
(counting) reading.  The strip-window identity `D = L + 2N` holds unconditionally on the actual
ξ-divisor: off-line zeros pair under the critical-line reflection with equal orders, so the total
order of a strip window is congruent mod 2 to its on-line part — a loop-level functional of the
window divisor at the square-root level can never see an off-line zero, which is exactly why the
certificate demands the per-zero refinement.
-/

open Complex Set Metric

namespace RHTower

/-! ## Per-point rung data -/

/-- Per-point form of the rung datum: for a ξ-zero, divisibility of the vanishing order by `2^k`
in `ℕ∞` is exactly the bound `k ≤ ladderHeight ρ` on the order's 2-adic valuation. -/
theorem xi_order_dvd_iff_le_ladderHeight {ρ : ℂ} (hzero : xi ρ = 0) (k : ℕ) :
    ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ ↔ k ≤ ladderHeight ρ := by
  have hcoe : analyticOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  constructor
  · intro h
    rw [hcoe] at h
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (xi_order_toNat_ne_zero hzero)).mp
      (natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) h)
  · intro h
    rw [hcoe]
    exact Nat.cast_dvd_cast ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (xi_order_toNat_ne_zero hzero)).mpr h)

/-- A ξ-zero has positive ladder height iff its vanishing order is even: the first rung is the
per-zero parity. -/
theorem ladderHeight_pos_iff_even {ρ : ℂ} (hzero : xi ρ = 0) :
    1 ≤ ladderHeight ρ ↔ Even (analyticOrderAt xi ρ).toNat := by
  unfold ladderHeight
  rw [even_iff_two_dvd, ← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (xi_order_toNat_ne_zero hzero), pow_one]

/-! ## The strip and box windows and their zero sets -/

/-- The strip window of height `T`: the full open critical strip `0 < Re < 1` truncated to heights
`0 ≤ Im < T`.  Closed under the critical-line reflection `lineReflect`. -/
def stripWindow (T : ℝ) : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im < T}

/-- The box window of height `T`: the right half `½ < Re < 1` of the strip window — the region
whose ξ-zeros the ladder constrains. -/
def boxWindow (T : ℝ) : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 ≤ s.im ∧ s.im < T}

/-- The ξ-zeros of the strip window of height `T`. -/
def stripZeros (T : ℝ) : Set ℂ := {ρ ∈ stripWindow T | xi ρ = 0}

/-- The ξ-zeros of the box window of height `T`. -/
def boxZeros (T : ℝ) : Set ℂ := {ρ ∈ boxWindow T | xi ρ = 0}

theorem boxZeros_subset_stripZeros (T : ℝ) : boxZeros T ⊆ stripZeros T := by
  rintro ρ ⟨⟨h1, h2, him0, himT⟩, hz⟩
  exact ⟨⟨by linarith, h2, him0, himT⟩, hz⟩

/-- A strip-window ξ-zero right of the critical line is a box-window zero. -/
theorem mem_boxZeros_of_stripZeros_right {T : ℝ} {ρ : ℂ} (h : ρ ∈ stripZeros T)
    (hre : 1 / 2 < ρ.re) : ρ ∈ boxZeros T :=
  ⟨⟨hre, h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩

/-- The strip window is bounded: it lies in a ball around `2`. -/
theorem stripWindow_subset_ball (T : ℝ) : stripWindow T ⊆ ball (2 : ℂ) (max T 0 + 2) := by
  rintro s ⟨h0, h1, him0, himT⟩
  rw [mem_ball, dist_eq_norm]
  calc ‖s - 2‖ ≤ |(s - 2).re| + |(s - 2).im| := norm_le_abs_re_add_abs_im _
    _ = |s.re - 2| + |s.im| := by simp
    _ < 2 + max T 0 := by
        have h2 : |s.re - 2| < 2 := by rw [abs_lt]; constructor <;> linarith
        have h3 : |s.im| < max T 0 := by
          rw [abs_of_nonneg him0]
          exact lt_of_lt_of_le himT (le_max_left T 0)
        linarith
    _ = max T 0 + 2 := by ring

/-- **Every strip window contains finitely many ξ-zeros** — the compact-exhaustion handle the
bounded windows supply and the half-plane denies. -/
theorem stripZeros_finite (T : ℝ) : (stripZeros T).Finite :=
  (xi_zeros_finite_ball 2 (max T 0 + 2)).subset
    fun _ hρ => ⟨stripWindow_subset_ball T hρ.1, hρ.2⟩

/-- Every box window contains finitely many ξ-zeros. -/
theorem boxZeros_finite (T : ℝ) : (boxZeros T).Finite :=
  (stripZeros_finite T).subset (boxZeros_subset_stripZeros T)

theorem boxZeros_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : boxZeros T₁ ⊆ boxZeros T₂ := by
  rintro ρ ⟨⟨h1, h2, him0, himT⟩, hz⟩
  exact ⟨⟨h1, h2, him0, lt_of_lt_of_le himT h⟩, hz⟩

theorem boxZeros_eq_empty_of_nonpos {T : ℝ} (hT : T ≤ 0) : boxZeros T = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ρ ⟨⟨-, -, him0, himT⟩, -⟩
  linarith

/-- The strip-window zero set is closed under the critical-line reflection: ξ's two symmetries
compose to `s ↦ 1 − s̄`, which preserves the strip, the height, and the zero set. -/
theorem lineReflect_mem_stripZeros {T : ℝ} {ρ : ℂ} (h : ρ ∈ stripZeros T) :
    lineReflect ρ ∈ stripZeros T := by
  obtain ⟨⟨h0, h1, him0, himT⟩, hz⟩ := h
  have him : (lineReflect ρ).im = ρ.im := by simp [lineReflect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [lineReflect_re]; linarith
  · rw [lineReflect_re]; linarith
  · rw [him]; exact him0
  · rw [him]; exact himT
  · simp only [lineReflect]
    rw [xi_one_sub, xi_conj, hz, map_zero]

/-! ## The height-window certificate -/

/-- **The height-window certificate**: every ξ-zero of the box window of height `T` has vanishing
order divisible by `2^k`.  Since the window's zero set is finite (`boxZeros_finite`), this is a
statement about finitely many vanishing orders. -/
def WindowCertificate (k : ℕ) (T : ℝ) : Prop :=
  ∀ ρ ∈ boxZeros T, ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ

theorem windowCertificate_zero (T : ℝ) : WindowCertificate 0 T := by
  intro ρ _
  simp only [pow_zero, Nat.cast_one, one_dvd]

theorem windowCertificate_of_nonpos {k : ℕ} {T : ℝ} (hT : T ≤ 0) : WindowCertificate k T := by
  intro ρ hρ
  rw [boxZeros_eq_empty_of_nonpos hT] at hρ
  exact absurd hρ (Set.notMem_empty ρ)

/-- Certificates restrict to lower windows: monotone in the height. -/
theorem windowCertificate_mono {k : ℕ} {T₁ T₂ : ℝ} (h : T₁ ≤ T₂)
    (hc : WindowCertificate k T₂) : WindowCertificate k T₁ :=
  fun ρ hρ => hc ρ (boxZeros_mono h hρ)

/-- Certificates descend to lower levels: antitone in the level. -/
theorem windowCertificate_of_le {m k : ℕ} (hmk : m ≤ k) {T : ℝ}
    (hc : WindowCertificate k T) : WindowCertificate m T :=
  fun ρ hρ => dvd_trans (Nat.cast_dvd_cast (pow_dvd_pow 2 hmk)) (hc ρ hρ)

/-- The certificate in terms of the 2-adic valuation: level `k` at height `T` holds iff every
box-window zero has ladder height at least `k`. -/
theorem windowCertificate_iff_ladderHeight (k : ℕ) (T : ℝ) :
    WindowCertificate k T ↔ ∀ ρ ∈ boxZeros T, k ≤ ladderHeight ρ :=
  forall₂_congr fun _ hρ => xi_order_dvd_iff_le_ladderHeight hρ.2 k

/-- The certificate is a finite check: a conjunction of height bounds over the finitely many
zeros of the window. -/
theorem windowCertificate_iff_finset (k : ℕ) (T : ℝ) :
    WindowCertificate k T ↔
      ∀ ρ ∈ (boxZeros_finite T).toFinset, k ≤ ladderHeight ρ := by
  rw [windowCertificate_iff_ladderHeight]
  constructor
  · intro h ρ hρ
    exact h ρ ((boxZeros_finite T).mem_toFinset.mp hρ)
  · intro h ρ hρ
    exact h ρ ((boxZeros_finite T).mem_toFinset.mpr hρ)

/-- The level-`1` certificate is the per-zero parity: no odd-order ξ-zero in the window. -/
theorem windowCertificate_one_iff_even (T : ℝ) :
    WindowCertificate 1 T ↔ ∀ ρ ∈ boxZeros T, Even (analyticOrderAt xi ρ).toNat := by
  rw [windowCertificate_iff_ladderHeight]
  exact forall₂_congr fun ρ hρ => ladderHeight_pos_iff_even hρ.2

/-! ## Exhaustion: the certificates decide the ladder and RH -/

/-- **Window exhaustion of the ladder.**  Rung `k` holds iff the height-`T` certificate holds at
every height: the box localization collapses the ladder to the family of finite certificates. -/
theorem rhLadder_iff_forall_windowCertificate (k : ℕ) :
    RHLadder k ↔ ∀ T : ℝ, WindowCertificate k T := by
  constructor
  · intro h T ρ hρ
    exact h ρ (mem_rightHalf.mpr hρ.1.1) hρ.2
  · intro h
    rw [rhLadder_iff_openStrip_upper]
    intro ρ h1 h2 him hz
    exact h (ρ.im + 1) ρ ⟨⟨h1, h2, him, lt_add_one ρ.im⟩, hz⟩

/-- Natural-number heights suffice: the ladder is decided by a countable sequence of finite
certificates. -/
theorem rhLadder_iff_forall_nat_windowCertificate (k : ℕ) :
    RHLadder k ↔ ∀ n : ℕ, WindowCertificate k n := by
  rw [rhLadder_iff_forall_windowCertificate]
  constructor
  · intro h n
    exact h n
  · intro h T
    exact windowCertificate_mono (Nat.le_ceil T) (h ⌈T⌉₊)

/-- **Cofinal heights suffice**: certificates at arbitrarily large heights give the rung. -/
theorem rhLadder_of_cofinal_windowCertificates {k : ℕ}
    (h : ∀ N : ℝ, ∃ T, N ≤ T ∧ WindowCertificate k T) : RHLadder k := by
  rw [rhLadder_iff_forall_windowCertificate]
  intro T
  obtain ⟨T', hT', hc⟩ := h T
  exact windowCertificate_mono hT' hc

/-- RH is the totality of the certificate family over both parameters. -/
theorem rh_iff_forall_windowCertificate :
    RiemannHypothesis ↔ ∀ (k : ℕ) (T : ℝ), WindowCertificate k T := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' fun k => rhLadder_iff_forall_windowCertificate k

/-- **The diagonal sequence decides RH.**  Both monotonicities compress the two-parameter family
to the diagonal: RH holds iff the level-`n` certificate holds at height `n` for every `n` — a
single countable sequence of statements, each about finitely many zeros. -/
theorem rh_iff_diagonal_windowCertificate :
    RiemannHypothesis ↔ ∀ n : ℕ, WindowCertificate n n := by
  constructor
  · intro h n
    exact (rhLadder_iff_forall_windowCertificate n).mp ((rh_iff_forall_ladder.mp h) n) n
  · intro h
    rw [rh_iff_forall_ladder]
    intro k
    rw [rhLadder_iff_forall_nat_windowCertificate]
    intro m
    exact windowCertificate_mono (Nat.cast_le.mpr (le_max_right k m))
      (windowCertificate_of_le (le_max_left k m) (h (max k m)))

/-- **Rung 1 through the windows**: no odd-order box-window ξ-zero at any height. -/
theorem rhLadder_one_iff_forall_window_even :
    RHLadder 1 ↔ ∀ T : ℝ, ∀ ρ ∈ boxZeros T, Even (analyticOrderAt xi ρ).toNat := by
  rw [rhLadder_iff_forall_windowCertificate]
  exact forall_congr' fun T => windowCertificate_one_iff_even T

/-! ## Sharp collapse per window -/

/-- A box-window zero breaks every certificate level strictly above its ladder height. -/
theorem not_windowCertificate_of_gt_ladderHeight {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ boxZeros T)
    {k : ℕ} (hk : ladderHeight ρ < k) : ¬ WindowCertificate k T := by
  intro hc
  rw [windowCertificate_iff_ladderHeight] at hc
  exact absurd (hc ρ hρ) (Nat.not_le.mpr hk)

/-- The exact first failing level of a window containing a zero of height `h` is `h + 1`. -/
theorem not_windowCertificate_ladderHeight_succ {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ boxZeros T) :
    ¬ WindowCertificate (ladderHeight ρ + 1) T :=
  not_windowCertificate_of_gt_ladderHeight hρ (Nat.lt_succ_self _)

/-- **All levels on one window ⟺ the window is zero-free**: the full dyadic tower of certificates
at a single height is exactly the absence of box zeros below that height. -/
theorem forall_windowCertificate_iff_boxZeros_empty (T : ℝ) :
    (∀ k, WindowCertificate k T) ↔ boxZeros T = ∅ := by
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro ρ hρ
    exact not_windowCertificate_ladderHeight_succ hρ (h (ladderHeight ρ + 1))
  · intro h k ρ hρ
    rw [h] at hρ
    exact absurd hρ (Set.notMem_empty ρ)

/-- RH as window emptiness: no box zeros below any height. -/
theorem rh_iff_forall_boxZeros_empty : RiemannHypothesis ↔ ∀ T : ℝ, boxZeros T = ∅ := by
  rw [rh_iff_forall_windowCertificate]
  constructor
  · intro h T
    exact (forall_windowCertificate_iff_boxZeros_empty T).mp (fun k => h k T)
  · intro h k T
    exact (forall_windowCertificate_iff_boxZeros_empty T).mpr (h T) k

/-! ## The per-window Kummer correspondence on truncated half-bands -/

/-- The truncated half-band `Re > ½`, `|Im| < T`: the convex bounded-height domain whose ξ-root
existence is decided by the height-`T` certificate. -/
def halfBand (T : ℝ) : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ |s.im| < T}

theorem halfBand_eq_inter (T : ℝ) :
    halfBand T = rightHalf ∩ ({s : ℂ | s.im < T} ∩ {s : ℂ | -T < s.im}) := by
  ext s
  simp only [halfBand, rightHalf, Set.mem_inter_iff, Set.mem_setOf_eq, abs_lt]
  tauto

theorem isOpen_halfBand (T : ℝ) : IsOpen (halfBand T) := by
  rw [halfBand_eq_inter]
  exact isOpen_rightHalf.inter ((isOpen_lt Complex.continuous_im continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im))

theorem convex_halfBand (T : ℝ) : Convex ℝ (halfBand T) := by
  rw [halfBand_eq_inter]
  exact convex_rightHalf.inter ((convex_halfSpace_im_lt T).inter (convex_halfSpace_im_gt (-T)))

theorem two_mem_halfBand {T : ℝ} (hT : 0 < T) : (2 : ℂ) ∈ halfBand T := by
  have h2re : (2 : ℂ).re = 2 := by simp
  have h2im : (2 : ℂ).im = 0 := by simp
  constructor
  · rw [h2re]; norm_num
  · rw [h2im]; simpa using hT

theorem halfBand_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : halfBand T₁ ⊆ halfBand T₂ :=
  fun _ hs => ⟨hs.1, lt_of_lt_of_le hs.2 h⟩

theorem halfBand_zeros_finite_in_ball (T : ℝ) (R : ℕ) :
    {s ∈ halfBand T ∩ ball (2 : ℂ) ((R : ℝ) + 1) | xi s = 0}.Finite :=
  (xi_zeros_finite_ball 2 ((R : ℝ) + 1)).subset fun _ hx => ⟨hx.1.2, hx.2⟩

/-- Order divisibility at every half-band zero is decided by the box window: `Re ≥ 1` is
zero-free and the lower half-band reflects into the box by conjugation with equal orders. -/
theorem forall_band_dvd_iff_windowCertificate (k : ℕ) (T : ℝ) :
    (∀ ρ ∈ halfBand T, xi ρ = 0 → ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ) ↔
      WindowCertificate k T := by
  constructor
  · rintro h ρ ⟨⟨h1, h2, him0, himT⟩, hz⟩
    exact h ρ ⟨h1, by rwa [abs_of_nonneg him0]⟩ hz
  · rintro hc ρ ⟨h1, himabs⟩ hz
    have h2 : ρ.re < 1 := by
      by_contra h2
      exact xi_ne_zero_of_one_le_re (not_lt.mp h2) hz
    by_cases him : 0 ≤ ρ.im
    · exact hc ρ ⟨⟨h1, h2, him, by rwa [abs_of_nonneg him] at himabs⟩, hz⟩
    · have him' : ρ.im < 0 := not_le.mp him
      have hconj_z : xi ((starRingEnd ℂ) ρ) = 0 := by rw [xi_conj, hz, map_zero]
      have hmem : (starRingEnd ℂ) ρ ∈ boxZeros T := by
        refine ⟨⟨?_, ?_, ?_, ?_⟩, hconj_z⟩
        · rwa [Complex.conj_re]
        · rwa [Complex.conj_re]
        · rw [Complex.conj_im]; linarith
        · rw [Complex.conj_im]
          have habs : |ρ.im| = -ρ.im := abs_of_neg him'
          linarith [habs ▸ himabs]
      have hres := hc _ hmem
      rwa [xi_orderAt_conj] at hres

/-- **The per-window Kummer correspondence.**  For positive height, the finite level-`k`
certificate holds iff ξ admits an analytic `2^k`-th root on the truncated half-band: the
bounded-region root obstruction is exactly the window's finitely many divisibility clauses. -/
theorem windowCertificate_iff_bandRoot {T : ℝ} (hT : 0 < T) (k : ℕ) :
    WindowCertificate k T ↔
      ∃ g, AnalyticOnNhd ℂ g (halfBand T) ∧ ∀ s ∈ halfBand T, g s ^ (2 : ℕ) ^ k = xi s := by
  rw [← forall_band_dvd_iff_windowCertificate k T]
  exact (exists_root_iff_orders_dvd (pow_pos two_pos k) (isOpen_halfBand T) (convex_halfBand T)
    (two_mem_halfBand hT) (xi_analyticOnNhd _) xi_two_ne_zero
    (halfBand_zeros_finite_in_ball T)).symm

/-- The level-`1` certificate is a square root of ξ on the truncated half-band. -/
theorem windowCertificate_one_iff_band_sqrt {T : ℝ} (hT : 0 < T) :
    WindowCertificate 1 T ↔
      ∃ g, AnalyticOnNhd ℂ g (halfBand T) ∧ ∀ s ∈ halfBand T, g s ^ (2 : ℕ) = xi s := by
  rw [windowCertificate_iff_bandRoot hT 1]
  simp only [pow_one]

/-- Band-root nesting: a `2^{k+1}`-th root on a half-band squares to a `2^k`-th root. -/
theorem bandRoot_of_succ {T : ℝ} {k : ℕ}
    (h : ∃ g, AnalyticOnNhd ℂ g (halfBand T) ∧ ∀ s ∈ halfBand T, g s ^ (2 : ℕ) ^ (k + 1) = xi s) :
    ∃ g, AnalyticOnNhd ℂ g (halfBand T) ∧ ∀ s ∈ halfBand T, g s ^ (2 : ℕ) ^ k = xi s := by
  obtain ⟨g, hg, hgpow⟩ := h
  refine ⟨fun s => g s ^ (2 : ℕ), hg.pow 2, fun s hs => ?_⟩
  calc (g s ^ (2 : ℕ)) ^ (2 : ℕ) ^ k = g s ^ (2 * 2 ^ k) := by rw [← pow_mul]
    _ = g s ^ (2 : ℕ) ^ (k + 1) := by rw [← pow_succ']
    _ = xi s := hgpow s hs

/-- Band-root restriction: a root on a taller band restricts to every lower band. -/
theorem bandRoot_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) {k : ℕ}
    (hr : ∃ g, AnalyticOnNhd ℂ g (halfBand T₂) ∧ ∀ s ∈ halfBand T₂, g s ^ (2 : ℕ) ^ k = xi s) :
    ∃ g, AnalyticOnNhd ℂ g (halfBand T₁) ∧ ∀ s ∈ halfBand T₁, g s ^ (2 : ℕ) ^ k = xi s := by
  obtain ⟨g, hg, hgpow⟩ := hr
  exact ⟨g, hg.mono (halfBand_mono h), fun s hs => hgpow s (halfBand_mono h hs)⟩

/-- **Band exhaustion of the ladder.**  Rung `k` — an analytic `2^k`-th root of ξ on the full
half-plane — holds iff ξ has a `2^k`-th root on every truncated half-band. -/
theorem rhLadder_iff_forall_bandRoot (k : ℕ) :
    RHLadder k ↔ ∀ T : ℝ, 0 < T →
      ∃ g, AnalyticOnNhd ℂ g (halfBand T) ∧ ∀ s ∈ halfBand T, g s ^ (2 : ℕ) ^ k = xi s := by
  rw [rhLadder_iff_forall_windowCertificate]
  constructor
  · intro h T hT
    exact (windowCertificate_iff_bandRoot hT k).mp (h T)
  · intro h T
    rcases le_or_gt T 0 with hT | hT
    · exact windowCertificate_of_nonpos hT
    · exact (windowCertificate_iff_bandRoot hT k).mpr (h T hT)

/-! ## The boundary (counting) face: the window divisor identity and its congruences -/

/-- **The window divisor identity `D = L + 2N` on the actual ξ-divisor**: the total vanishing
order of a strip window equals its on-line part plus twice its box part.  Closure and
multiplicity-invariance under the critical-line reflection are theorems of ξ here, not
hypotheses. -/
theorem stripWindow_order_identity (T : ℝ) :
    ∑ ρ ∈ (stripZeros_finite T).toFinset, (analyticOrderAt xi ρ).toNat =
      ∑ ρ ∈ (stripZeros_finite T).toFinset.filter (fun ρ => ρ.re = 1 / 2),
        (analyticOrderAt xi ρ).toNat +
      2 * ∑ ρ ∈ (stripZeros_finite T).toFinset.filter (fun ρ => 1 / 2 < ρ.re),
        (analyticOrderAt xi ρ).toNat := by
  refine window_identity (m := fun ρ => (analyticOrderAt xi ρ).toNat) ?_ ?_
  · intro z hz
    rw [Set.Finite.mem_toFinset] at hz ⊢
    exact lineReflect_mem_stripZeros hz
  · intro z _
    exact congrArg ENat.toNat (xi_orderAt_lineReflect z)

/-- **The line carries the loop parity.**  The total ξ-order of a strip window is congruent mod 2
to its on-line part: off-line zeros pair under the critical-line reflection with equal orders, so
a mod-2 (loop-level) functional of the window divisor can never see an off-line zero.  The
certificate's per-zero parity is therefore strictly finer data than any single window total. -/
theorem stripWindow_parity (T : ℝ) :
    ∑ ρ ∈ (stripZeros_finite T).toFinset, (analyticOrderAt xi ρ).toNat ≡
      ∑ ρ ∈ (stripZeros_finite T).toFinset.filter (fun ρ => ρ.re = 1 / 2),
        (analyticOrderAt xi ρ).toNat [MOD 2] := by
  rw [stripWindow_order_identity T]
  exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr
    (by rw [Nat.add_sub_cancel_left]; exact dvd_mul_right 2 _)).symm

/-- The right-half part of the strip-window divisor is exactly the box-window divisor. -/
theorem stripZeros_toFinset_filter_right (T : ℝ) :
    (stripZeros_finite T).toFinset.filter (fun ρ => 1 / 2 < ρ.re)
      = (boxZeros_finite T).toFinset := by
  ext ρ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hs, hre⟩
    exact mem_boxZeros_of_stripZeros_right hs hre
  · intro hb
    exact ⟨boxZeros_subset_stripZeros T hb, hb.1.1⟩

/-- **Certificate ⟹ window congruence.**  The height-`T` level-`k` certificate forces the
concrete congruence `D ≡ L (mod 2^{k+1})` on the same window: only the window's own finitely
many zeros enter. -/
theorem stripWindow_modEq_of_windowCertificate {k : ℕ} {T : ℝ}
    (hc : WindowCertificate k T) :
    ∑ ρ ∈ (stripZeros_finite T).toFinset, (analyticOrderAt xi ρ).toNat ≡
      ∑ ρ ∈ (stripZeros_finite T).toFinset.filter (fun ρ => ρ.re = 1 / 2),
        (analyticOrderAt xi ρ).toNat [MOD 2 ^ (k + 1)] := by
  rw [window_modEq_iff (stripWindow_order_identity T), stripZeros_toFinset_filter_right T]
  refine Finset.dvd_sum ?_
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  have hdvd := hc ρ hρ
  have hcoe : analyticOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  rw [hcoe] at hdvd
  exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd

/-- **Certificate ⟺ sub-window congruences.**  The level-`k` height-`T` certificate holds iff
EVERY reflection-closed sub-configuration of the window's ξ-divisor satisfies the mod-`2^{k+1}`
congruence between its total and on-line orders.  Forward: the identity `D = L + 2N` reduces the
congruence to divisibility of the box sum, which the certificate gives term by term.  Backward:
the two-point sub-window of a box zero and its reflection reads that zero's own order.  The single
full-window congruence constrains only the SUM of the box orders — the per-zero refinement is
exactly what the sub-window quantifier adds. -/
theorem windowCertificate_iff_subWindow_congruences (k : ℕ) (T : ℝ) :
    WindowCertificate k T ↔
      ∀ t : Finset ℂ, ↑t ⊆ stripZeros T → (∀ z ∈ t, lineReflect z ∈ t) →
        (∑ ρ ∈ t, (analyticOrderAt xi ρ).toNat ≡
          ∑ ρ ∈ t.filter (fun ρ => ρ.re = 1 / 2),
            (analyticOrderAt xi ρ).toNat [MOD 2 ^ (k + 1)]) := by
  constructor
  · intro hc t hsub hclosed
    have hID := window_identity (m := fun ρ => (analyticOrderAt xi ρ).toNat) hclosed
      (fun z _ => congrArg ENat.toNat (xi_orderAt_lineReflect z))
    rw [window_modEq_iff hID]
    refine Finset.dvd_sum ?_
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    have hmem : ρ ∈ boxZeros T := mem_boxZeros_of_stripZeros_right (hsub hρ.1) hρ.2
    have hdvd := hc ρ hmem
    have hcoe : analyticOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
      (ENat.coe_toNat (xi_order_ne_top ρ)).symm
    rw [hcoe] at hdvd
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd
  · intro h ρ hρ
    have hoff : 1 / 2 < ρ.re := hρ.1.1
    have hρstrip : ρ ∈ stripZeros T := boxZeros_subset_stripZeros T hρ
    have hne : ρ ≠ lineReflect ρ := by
      intro he
      have hre := congrArg Complex.re he
      rw [lineReflect_re] at hre
      linarith
    have hsub : ↑({ρ, lineReflect ρ} : Finset ℂ) ⊆ stripZeros T := by
      intro z hz
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hρstrip
      · exact lineReflect_mem_stripZeros hρstrip
    have hclosed : ∀ z ∈ ({ρ, lineReflect ρ} : Finset ℂ),
        lineReflect z ∈ ({ρ, lineReflect ρ} : Finset ℂ) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with rfl | rfl
      · exact Or.inr rfl
      · rw [lineReflect_involutive]
        exact Or.inl rfl
    have hfilter : ({ρ, lineReflect ρ} : Finset ℂ).filter (fun z => z.re = 1 / 2) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl)
      · intro hz
        linarith
      · rw [lineReflect_re]
        intro hz
        linarith
    have hrel := h ({ρ, lineReflect ρ} : Finset ℂ) hsub hclosed
    rw [Finset.sum_pair hne, xi_orderAt_lineReflect, hfilter, Finset.sum_empty, ← two_mul,
      Nat.modEq_zero_iff_dvd, pow_succ, mul_comm (2 ^ k) 2,
      mul_dvd_mul_iff_left two_ne_zero] at hrel
    have hcoe : analyticOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
      (ENat.coe_toNat (xi_order_ne_top ρ)).symm
    rw [hcoe]
    exact Nat.cast_dvd_cast hrel

/-- **RH through finite sub-window congruences.**  RH holds iff at every level and height, every
reflection-closed sub-configuration of the strip window's ξ-divisor satisfies the dyadic
congruence between its total and on-line orders. -/
theorem rh_iff_forall_subWindow_congruences :
    RiemannHypothesis ↔
      ∀ (k : ℕ) (T : ℝ), ∀ t : Finset ℂ, ↑t ⊆ stripZeros T →
        (∀ z ∈ t, lineReflect z ∈ t) →
        (∑ ρ ∈ t, (analyticOrderAt xi ρ).toNat ≡
          ∑ ρ ∈ t.filter (fun ρ => ρ.re = 1 / 2),
            (analyticOrderAt xi ρ).toNat [MOD 2 ^ (k + 1)]) := by
  rw [rh_iff_forall_windowCertificate]
  exact forall₂_congr fun k T => windowCertificate_iff_subWindow_congruences k T

end RHTower

namespace RHTower

open Complex Set Metric

/-- **Certificate from an on-line ball cover.**  If every box-window zero lies in some ball whose
ξ-zeros are all on the critical line, the certificate holds at every level — vacuously: each
covering ball certifies that its box zero cannot exist.  This is the consumer interface for the
on-line counting instruments, which produce exactly such balls from certified line sign data. -/
theorem windowCertificate_of_ball_online_cover {k : ℕ} {T : ℝ}
    (h : ∀ ρ ∈ boxZeros T, ∃ a R, ρ ∈ ball a R ∧ ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2) :
    WindowCertificate k T := by
  intro ρ hρ
  obtain ⟨a, R, hball, honline⟩ := h ρ hρ
  exact absurd (honline ρ hball hρ.2) (ne_of_gt hρ.1.1)

/-- Rung `k` from on-line ball covers of every window. -/
theorem rhLadder_of_ball_online_covers (k : ℕ)
    (h : ∀ T : ℝ, ∀ ρ ∈ boxZeros T, ∃ a R, ρ ∈ ball a R ∧
      ∀ p ∈ ball a R, xi p = 0 → p.re = 1 / 2) : RHLadder k := by
  rw [rhLadder_iff_forall_windowCertificate]
  exact fun T => windowCertificate_of_ball_online_cover (h T)

/-- **Band-root rigidity.**  Two analytic `2^k`-th roots of ξ on the same positive-height band
that agree at the anchor `2` agree on the whole band. -/
theorem bandRoot_unique {T : ℝ} (hT : 0 < T) {k : ℕ} {g₁ g₂ : ℂ → ℂ}
    (h₁ : AnalyticOnNhd ℂ g₁ (halfBand T)) (h₂ : AnalyticOnNhd ℂ g₂ (halfBand T))
    (hp₁ : ∀ s ∈ halfBand T, g₁ s ^ (2 : ℕ) ^ k = xi s)
    (hp₂ : ∀ s ∈ halfBand T, g₂ s ^ (2 : ℕ) ^ k = xi s)
    (hval : g₁ 2 = g₂ 2) : Set.EqOn g₁ g₂ (halfBand T) :=
  pow_root_unique (pow_pos two_pos k) (isOpen_halfBand T) (convex_halfBand T).isPreconnected
    h₁ h₂ hp₁ hp₂ (two_mem_halfBand hT) xi_two_ne_zero hval

end RHTower

namespace RHTower

open Complex Set Metric

/-- Nonvanishing of ξ on the truncated half-band is exactly the emptiness of the box window:
`Re ≥ 1` is unconditionally zero-free and the lower half-band reflects into the box by
conjugation. -/
theorem forall_band_ne_zero_iff_boxZeros_empty {T : ℝ} :
    (∀ z ∈ halfBand T, xi z ≠ 0) ↔ boxZeros T = ∅ := by
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ρ ⟨⟨h1, h2, him0, himT⟩, hz⟩
    exact h ρ ⟨h1, by rwa [abs_of_nonneg him0]⟩ hz
  · intro h z hz hz0
    obtain ⟨h1, himabs⟩ := hz
    have h2 : z.re < 1 := by
      by_contra h2
      exact xi_ne_zero_of_one_le_re (not_lt.mp h2) hz0
    by_cases him : 0 ≤ z.im
    · have hmem : z ∈ boxZeros T :=
        ⟨⟨h1, h2, him, by rwa [abs_of_nonneg him] at himabs⟩, hz0⟩
      rw [h] at hmem
      exact absurd hmem (Set.notMem_empty z)
    · have him' : z.im < 0 := not_le.mp him
      have hcz : xi ((starRingEnd ℂ) z) = 0 := by rw [xi_conj, hz0, map_zero]
      have hmem : (starRingEnd ℂ) z ∈ boxZeros T := by
        refine ⟨⟨?_, ?_, ?_, ?_⟩, hcz⟩
        · rwa [Complex.conj_re]
        · rwa [Complex.conj_re]
        · rw [Complex.conj_im]; linarith
        · rw [Complex.conj_im]
          have habs : |z.im| = -z.im := abs_of_neg him'
          linarith [habs ▸ himabs]
      rw [h] at hmem
      exact absurd hmem (Set.notMem_empty _)

/-- **The windowed coherent tower.**  For positive height, the full ℤ₂-Kummer tower of ξ exists
on the truncated half-band iff the box window is empty of ξ-zeros — the bounded-height form of
the statement that the coherent tower on the half-plane is RH. -/
theorem coherentTower_halfBand_iff_boxZeros_empty {T : ℝ} (hT : 0 < T) :
    Nonempty (CoherentTower xi (halfBand T)) ↔ boxZeros T = ∅ := by
  rw [coherentTower_iff_nonvanishing (isOpen_halfBand T)
    (isSimplyConnected_of_convex (convex_halfBand T) ⟨2, two_mem_halfBand hT⟩)
    (convex_halfBand T).isPreconnected (xi_analyticOnNhd _) (two_mem_halfBand hT)
    xi_two_ne_zero]
  exact forall_band_ne_zero_iff_boxZeros_empty

/-- The windowed tower is the totality of the height-`T` certificates. -/
theorem coherentTower_halfBand_iff_forall_windowCertificate {T : ℝ} (hT : 0 < T) :
    Nonempty (CoherentTower xi (halfBand T)) ↔ ∀ k, WindowCertificate k T := by
  rw [coherentTower_halfBand_iff_boxZeros_empty hT]
  exact (forall_windowCertificate_iff_boxZeros_empty T).symm

/-- RH ⟺ the windowed coherent tower exists at every positive height. -/
theorem rh_iff_forall_coherentTower_halfBand :
    RiemannHypothesis ↔ ∀ T : ℝ, 0 < T → Nonempty (CoherentTower xi (halfBand T)) := by
  rw [rh_iff_forall_boxZeros_empty]
  constructor
  · intro h T hT
    exact (coherentTower_halfBand_iff_boxZeros_empty hT).mpr (h T)
  · intro h T
    rcases le_or_gt T 0 with hT | hT
    · exact boxZeros_eq_empty_of_nonpos hT
    · exact (coherentTower_halfBand_iff_boxZeros_empty hT).mp (h T hT)

end RHTower

namespace RHTower

open Complex Set Metric

/-- **Band roots form a coherent system across heights**: a `2^k`-th root of ξ on a lower band
and one on a taller band agreeing at the anchor `2` agree on the whole lower band.  Together with
`bandRoot_mono` and `bandRoot_unique` this makes the normalized band roots a compatible family
over the height exhaustion, whose totality is the half-plane root of `rhLadder_iff_root`. -/
theorem bandRoot_restrict_eq {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (h : T₁ ≤ T₂) {k : ℕ}
    {g₁ g₂ : ℂ → ℂ}
    (h₁ : AnalyticOnNhd ℂ g₁ (halfBand T₁)) (h₂ : AnalyticOnNhd ℂ g₂ (halfBand T₂))
    (hp₁ : ∀ s ∈ halfBand T₁, g₁ s ^ (2 : ℕ) ^ k = xi s)
    (hp₂ : ∀ s ∈ halfBand T₂, g₂ s ^ (2 : ℕ) ^ k = xi s)
    (hval : g₁ 2 = g₂ 2) : Set.EqOn g₁ g₂ (halfBand T₁) :=
  bandRoot_unique hT₁ h₁ (h₂.mono (halfBand_mono h)) hp₁
    (fun s hs => hp₂ s (halfBand_mono h hs)) hval

end RHTower
