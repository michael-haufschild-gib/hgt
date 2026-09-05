import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleSecondConvergence
import GaloisForLFunctions.RHTower.EulerDeletionFactorizationGraded
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Arithmetic conservation under moving chronological schedules

At a right-half zeta zero, literal deletion prefixes have Abel decay. A single positive lower
bound on the inner/outer cutoff ratio makes every moving chronological row uniformly dominated
by a summable doubled-abscissa tail. Stabilizing rows therefore retain their exact ordered limit.

For a singleton source and its squarefree interaction, the inclusive-minus-strict boundary is
the original strictly positive Mellin grade-mixing charge. This remains true for explicit moving
source schedules and for every schedule satisfying the stated relative bound. No weight recovery,
zero-dependent subtraction, or equality of the two chronological orientations is used.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower.DeletionSchedule

def row (x y : ℕ → ℂ) (k n : ℕ) : ℂ :=
  (∑ m ∈ Finset.range k, x m) * star (y n)

def scheduledPrefix (x y : ℕ → ℂ) (K : ℕ → ℕ → ℕ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, row x y (K N n) n

theorem row_bound {x y : ℕ → ℂ} {A B c σ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hσ : 0 ≤ σ)
    (hx : ∀ k, ‖∑ m ∈ Finset.range k, x m‖ ≤ A * ((k : ℝ)+1)^(-σ))
    (hy : ∀ n, ‖y n‖ ≤ B * ((n : ℝ)+1)^(-σ))
    {k n : ℕ} (hk : c*((n : ℝ)+1) ≤ (k : ℝ)+1) :
    ‖row x y k n‖ ≤ (A*B*c^(-σ))*((n : ℝ)+1)^(-2*σ) := by
  have hr := Real.rpow_le_rpow_of_nonpos (mul_pos hc (by positivity)) hk
    (neg_nonpos.mpr hσ)
  rw [Real.mul_rpow hc.le (by positivity)] at hr
  calc
    ‖row x y k n‖ = ‖∑ m ∈ Finset.range k, x m‖ * ‖y n‖ := by
      simp only [row, norm_mul, norm_star]
    _ ≤ (A*((k : ℝ)+1)^(-σ)) * (B*((n : ℝ)+1)^(-σ)) :=
      mul_le_mul (hx k) (hy n) (norm_nonneg _) (by positivity)
    _ ≤ (A*(c^(-σ)*((n : ℝ)+1)^(-σ))) * (B*((n : ℝ)+1)^(-σ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hA) (by positivity)
    _ = (A*B*c^(-σ))*((n : ℝ)+1)^(-2*σ) := by
      rw [show -2*σ = -σ + -σ by ring, Real.rpow_add (by positivity)]
      ring

theorem summable_majorant {σ : ℝ} (hσ : 1/2 < σ) (C : ℝ) :
    Summable (fun n : ℕ => C*((n : ℝ)+1)^(-2*σ)) := by
  have h : Summable (fun n : ℕ => (n : ℝ)^(-2*σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hh := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-2*σ)) 1).2 h
  simpa only [Nat.cast_add, Nat.cast_one] using hh.mul_left C

/-- One common relative lower cutoff controls every moving schedule; no upper cutoff bound
is required. The row limits retain strict versus inclusive diagonal incidence. -/
theorem tendsto_scheduledPrefix {x y : ℕ → ℂ} {A B c σ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hσ : 1/2 < σ)
    (hx : ∀ k, ‖∑ m ∈ Finset.range k, x m‖ ≤ A * ((k : ℝ)+1)^(-σ))
    (hy : ∀ n, ‖y n‖ ≤ B * ((n : ℝ)+1)^(-σ))
    (K : ℕ → ℕ → ℕ) (k : ℕ → ℕ)
    (hcone : ∀ (N n : ℕ), c*((n : ℝ)+1) ≤ (K N n : ℝ)+1)
    (hstable : ∀ n, ∀ᶠ N in atTop, K N n = k n) :
    Tendsto (scheduledPrefix x y K) atTop (nhds (∑' n, row x y (k n) n)) := by
  classical
  let f : ℕ → ℕ → ℂ := fun N n => if n < N then row x y (K N n) n else 0
  have hlim : ∀ n, Tendsto (fun N => f N n) atTop (nhds (row x y (k n) n)) := by
    intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [hstable n, eventually_gt_atTop n] with N hN hn
    simp [f, hn, hN]
  have hb : ∀ᶠ N in atTop, ∀ n,
      ‖f N n‖ ≤ (A*B*c^(-σ))*((n : ℝ)+1)^(-2*σ) := by
    filter_upwards [] with N n
    dsimp [f]
    split_ifs
    · exact row_bound hA hB hc (by linarith) hx hy (hcone N n)
    · simp only [norm_zero]
      positivity
  have ht := tendsto_tsum_of_dominated_convergence
    (summable_majorant hσ (A*B*c^(-σ))) hlim hb
  apply ht.congr
  intro N
  change (∑' n, f N n) = scheduledPrefix x y K N
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [f, Finset.mem_range.mp hn]
  · intro n hn
    simp [f, Finset.mem_range] at hn ⊢
    omega

theorem summable_row {x y : ℕ → ℂ} {A B c σ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hσ : 1/2 < σ)
    (hx : ∀ k, ‖∑ m ∈ Finset.range k, x m‖ ≤ A * ((k : ℝ)+1)^(-σ))
    (hy : ∀ n, ‖y n‖ ≤ B * ((n : ℝ)+1)^(-σ))
    (k : ℕ → ℕ) (hk : ∀ (n : ℕ), c*((n : ℝ)+1) ≤ (k n : ℝ)+1) :
    Summable (fun n => row x y (k n) n) :=
  (summable_majorant hσ (A*B*c^(-σ))).of_norm_bounded
    (fun n => row_bound hA hB hc (by linarith) hx hy (hk n))

theorem row_succ (x y : ℕ → ℂ) (n : ℕ) :
    row x y (n+1) n = row x y n n + x n * star (y n) := by
  simp only [row, Finset.sum_range_succ, add_mul]

/-- The two orientations differ by the literal diagonal, with its original weights. -/
theorem inclusive_sub_strict {x y : ℕ → ℂ}
    (hstrict : Summable (fun n => row x y n n))
    (hdiag : Summable (fun n => x n * star (y n))) :
    (∑' n, row x y (n+1) n) - (∑' n, row x y n n) = ∑' n, x n * star (y n) := by
  simp_rw [row_succ]
  rw [hstrict.tsum_add hdiag]
  abel

/-- Squarefree interaction, with the Mellin weight applied exactly once. -/
def interactionJump (p q : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  eulerDeletionDirichletCoefficient p n * eulerDeletionWeightedJump q s n

theorem norm_interactionJump_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (s : ℂ) (n : ℕ) :
    ‖interactionJump p q s n‖ ≤ (p : ℝ)*q*((n : ℝ)+1)^(-s.re) := by
  rw [interactionJump, norm_mul]
  calc
    _ ≤ (p : ℝ)*((q : ℝ)*((n : ℝ)+1)^(-s.re)) :=
      mul_le_mul (norm_eulerDeletionDirichletCoefficient_le hp n)
        (norm_eulerDeletionWeightedJump_le hq s n) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem weightedJump_eq_source (q : ℕ) (s : ℂ) (n : ℕ) :
    eulerDeletionWeightedJump q s n = deletionMellinSource (q+1) s (n+1) := by
  simp [eulerDeletionWeightedJump, eulerDeletionDirichletCoefficient, deletionMellinSource]

theorem interaction_diagonal {s : ℂ} (hs : 1/2 < s.re) (p q n : ℕ) :
    eulerDeletionWeightedJump q s n * star (interactionJump p q s n) =
      (((blockDeletionCoefficient (q+1) (n+1) : ℝ) *
        (deletionFactorizationInteraction (p+1) (q+1) (n+1) : ℝ) *
        deletionDirichletWeight (2*s.re) (n+1) : ℝ) : ℂ) := by
  have hstar : star (eulerDeletionDirichletCoefficient p n) =
      eulerDeletionDirichletCoefficient p n := by
    simp [eulerDeletionDirichletCoefficient]
  rw [interactionJump, star_mul', hstar]
  calc
    _ = eulerDeletionDirichletCoefficient p n *
        (eulerDeletionWeightedJump q s n * star (eulerDeletionWeightedJump q s n)) := by ring
    _ = _ := by
      rw [weightedJump_eq_source, deletionMellinSource_pair hs]
      simp only [eulerDeletionDirichletCoefficient, deletionFactorizationInteraction]
      push_cast
      ring

theorem summable_interaction_diagonal {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {s : ℂ} (hs : 1/2 < s.re) :
    Summable (fun n => eulerDeletionWeightedJump q s n * star (interactionJump p q s n)) := by
  apply ((summable_quadraticEnergy_eulerDeletionWeightedJump hq hs).mul_left (p : ℝ)).of_norm_bounded
  intro n
  rw [interactionJump, norm_mul, norm_star, norm_mul, Complex.normSq_eq_norm_sq]
  calc
    _ = ‖eulerDeletionDirichletCoefficient p n‖ * ‖eulerDeletionWeightedJump q s n‖^2 := by ring
    _ ≤ (p : ℝ) * ‖eulerDeletionWeightedJump q s n‖^2 :=
      mul_le_mul_of_nonneg_right (norm_eulerDeletionDirichletCoefficient_le hp n) (sq_nonneg _)

/-- Exact singleton/interaction collision charge, including the natural-index shift. -/
theorem tsum_interaction_diagonal {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {s : ℂ} (hs : 1/2 < s.re) :
    (∑' n, eulerDeletionWeightedJump q s n * star (interactionJump p q s n)) =
      (deletionFactorizationGradeCross (2*s.re) (p+1) (q+1) : ℂ) := by
  let f : ℕ → ℝ := fun n => (blockDeletionCoefficient (q+1) n : ℝ) *
    (deletionFactorizationInteraction (p+1) (q+1) n : ℝ) * deletionDirichletWeight (2*s.re) n
  have hpoint (n : ℕ) : eulerDeletionWeightedJump q s n * star (interactionJump p q s n) =
      (f (n+1) : ℂ) := interaction_diagonal hs p q n
  have hshift : Summable (fun n => f (n+1)) := Complex.summable_ofReal.mp
    ((summable_interaction_diagonal hp hq hs).congr hpoint)
  have hf : Summable f := (summable_nat_add_iff 1).mp hshift
  have hzero : f 0 = 0 := by
    simp [f, deletionDirichletWeight, Real.zero_rpow (by linarith : -(2*s.re) ≠ 0)]
  have hshiftSum : (∑' n, f (n+1)) = ∑' n, f n := by
    simpa [hzero] using hf.sum_add_tsum_nat_add 1
  simp_rw [hpoint]
  rw [← Complex.ofReal_tsum, hshiftSum]
  rfl

/-- All cofinal schedules staying above one positive relative cutoff preserve the same
source-selected strict/inclusive collision charge at a hypothetical right-half zeta zero. -/
theorem source_schedule_boundary {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {ρ : ℂ} (hρ : 1/2 < ρ.re) (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0)
    {c : ℝ} (hc : 0 < c) (Kminus Kplus : ℕ → ℕ → ℕ)
    (hminus : ∀ (N n : ℕ), c*((n : ℝ)+1) ≤ (Kminus N n : ℝ)+1)
    (hplus : ∀ (N n : ℕ), c*((n : ℝ)+1) ≤ (Kplus N n : ℝ)+1)
    (hminus_lim : ∀ n, ∀ᶠ N in atTop, Kminus N n = n)
    (hplus_lim : ∀ n, ∀ᶠ N in atTop, Kplus N n = n+1) :
    Tendsto (fun N =>
      scheduledPrefix (eulerDeletionWeightedJump q ρ) (interactionJump p q ρ) Kplus N -
      scheduledPrefix (eulerDeletionWeightedJump q ρ) (interactionJump p q ρ) Kminus N)
      atTop (nhds (deletionFactorizationGradeCross (2*ρ.re) (p+1) (q+1) : ℂ)) := by
  have hσ : 0 < ρ.re := by linarith
  have hA : 0 ≤ eulerDeletionAbelTailConstant q ρ := by
    unfold eulerDeletionAbelTailConstant
    positivity
  have hB : 0 ≤ (p : ℝ)*q := by positivity
  have hx := fun k => norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero q k hσ hρ1 hz
  have hy := norm_interactionJump_le hp hq ρ
  have hm := tendsto_scheduledPrefix hA hB hc hρ hx hy Kminus (fun n => n) hminus hminus_lim
  have hp' := tendsto_scheduledPrefix hA hB hc hρ hx hy Kplus (fun n => n+1) hplus hplus_lim
  have hstrict := summable_row hA hB (by norm_num : (0 : ℝ) < 1) hρ hx hy
    (fun n => n) (by intro n; simp)
  have hid := inclusive_sub_strict hstrict (summable_interaction_diagonal hp hq hρ)
  rw [tsum_interaction_diagonal hp hq hρ] at hid
  simpa only [hid] using hp'.sub hm

/-- The retained boundary is strictly positive for actual coprime source labels; zero closure
does not supply its annihilation. -/
theorem source_boundary_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime (p+1) (q+1)) {s : ℂ} (hs : 1/2 < s.re) :
    0 < deletionFactorizationGradeCross (2*s.re) (p+1) (q+1) :=
  deletionFactorizationGradeCross_pos_of_coprime (by linarith) (by omega) (by omega) hpq

/-- Explicit expanding lower and shrinking upper chronological regions. -/
def lowerSchedule (N n : ℕ) : ℕ := n - n / (N+2)

def upperSchedule (N n : ℕ) : ℕ := n + 1 + n / (N+2)

theorem lowerSchedule_cone (N n : ℕ) :
    (1/2 : ℝ)*((n : ℝ)+1) ≤ (lowerSchedule N n : ℝ)+1 := by
  have hd : n / (N+2) ≤ n / 2 := Nat.div_le_div_left (by omega) (by omega)
  have hn : n ≤ 2 * lowerSchedule N n := by
    unfold lowerSchedule
    omega
  have hnR : (n : ℝ) ≤ 2 * (lowerSchedule N n : ℝ) := by exact_mod_cast hn
  linarith

theorem upperSchedule_cone (N n : ℕ) :
    (1/2 : ℝ)*((n : ℝ)+1) ≤ (upperSchedule N n : ℝ)+1 := by
  have hn : n ≤ upperSchedule N n :=
    (Nat.le_add_right n 1).trans (Nat.le_add_right (n+1) (n/(N+2)))
  have hnR : (n : ℝ) ≤ (upperSchedule N n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  linarith

theorem lowerSchedule_stable (n : ℕ) :
    ∀ᶠ N in atTop, lowerSchedule N n = n := by
  filter_upwards [eventually_ge_atTop n] with N hN
  simp [lowerSchedule, Nat.div_eq_of_lt (by omega : n < N+2)]

theorem upperSchedule_stable (n : ℕ) :
    ∀ᶠ N in atTop, upperSchedule N n = n+1 := by
  filter_upwards [eventually_ge_atTop n] with N hN
  simp [upperSchedule, Nat.div_eq_of_lt (by omega : n < N+2)]

/-- A finite source-defined schedule pair, chosen before any zero, retains the strictly
positive original weighted collision boundary after hypothetical right-half zero landing. -/
theorem canonical_source_boundary {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime (p+1) (q+1))
    {ρ : ℂ} (hρ : 1/2 < ρ.re) (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    Tendsto (fun N =>
      scheduledPrefix (eulerDeletionWeightedJump q ρ) (interactionJump p q ρ) upperSchedule N -
      scheduledPrefix (eulerDeletionWeightedJump q ρ) (interactionJump p q ρ) lowerSchedule N)
      atTop (nhds (deletionFactorizationGradeCross (2*ρ.re) (p+1) (q+1) : ℂ)) ∧
    0 < deletionFactorizationGradeCross (2*ρ.re) (p+1) (q+1) := by
  exact ⟨source_schedule_boundary hp hq hρ hρ1 hz (by norm_num : (0 : ℝ) < 1/2)
    lowerSchedule upperSchedule lowerSchedule_cone upperSchedule_cone
    lowerSchedule_stable upperSchedule_stable, source_boundary_pos hp hq hpq hρ⟩

end RHTower.DeletionSchedule

