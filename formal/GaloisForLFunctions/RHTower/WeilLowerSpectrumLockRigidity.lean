import GaloisForLFunctions.RHTower.WeilInnerLockRigidity
import GaloisForLFunctions.RHTower.WeilBoundedSpectrumLockRigidity
import GaloisForLFunctions.HTGeometry.BohrParseval
import GaloisForLFunctions.HTGeometry.BohrMeanMonotone

/-!
# Locks with spectrum below one

**Theorem** (`lower_spectrum_lock_rigidity`).  Let `G` be a Herglotz producer for the weights `lam`
with lower-line lock `G(1 − s) = V(s) G(s)`, `s = ½ + 2iτ`, `τ < 0`, where

`V(s) = Σ_j q_j ρ_j^{−(s−½)}`,  `0 < ρ_j ≤ 1`,  `Σ_j |q_j| ρ_j^{−δ} < ∞` for some `δ > 0`.

Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds.  The frequencies `ρ_j` are
arbitrary in `(0, 1]`: rational (`1/k`, `p/q < 1`) or irrational.

**Proof.**
* `V` is holomorphic on `Re s < ½ + δ` and bounded by `Σ|q_j|` on `Re s ≤ ½`.
* `|V| = 1` on the lower line (`norm_lock_eq_one`).  On the line `y ↦ V(½ − iy)` is an absolutely
  convergent exponential sum, so `|V(½ − iy)| − 1` is almost periodic; it vanishes for `y > 0`, hence
  everywhere (`eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero`).
* Phragmén–Lindelöf on the half-plane `Re s < ½` gives `|V| ≤ 1` there.
* `V` is an inner lock, and `inner_lock_rigidity` applies.
-/

open Complex Filter Topology Set Asymptotics
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- The lock with frequencies `ρ_j`. -/
def lowLock (q : ℕ → ℂ) (ρ : ℕ → ℝ) (s : ℂ) : ℂ := ∑' j, q j * (ρ j : ℂ) ^ (-(s - 1 / 2))

theorem norm_lowLock_term {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ‖(r : ℂ) ^ (-(s - 1 / 2))‖ = r ^ (-(s.re - 1 / 2)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

theorem norm_lowLock_term_le {r δ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {s : ℂ}
    (hs : s.re < 1 / 2 + δ) : ‖(r : ℂ) ^ (-(s - 1 / 2))‖ ≤ r ^ (-δ) := by
  rw [norm_lowLock_term hr0]
  exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)

theorem norm_lowLock_term_le_one {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {s : ℂ}
    (hs : s.re ≤ 1 / 2) : ‖(r : ℂ) ^ (-(s - 1 / 2))‖ ≤ 1 := by
  rw [norm_lowLock_term hr0]
  exact Real.rpow_le_one hr0.le hr1 (by linarith)

theorem summable_norm_of_lowLock {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ0 : ∀ j, 0 < ρ j)
    (hρ1 : ∀ j, ρ j ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hq : Summable fun j => ‖q j‖ * ρ j ^ (-δ)) :
    Summable fun j => ‖q j‖ :=
  Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => le_mul_of_one_le_right (norm_nonneg _)
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hρ0 j) (hρ1 j) (by linarith))) hq

theorem differentiableOn_lowLock {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ0 : ∀ j, 0 < ρ j)
    (hρ1 : ∀ j, ρ j ≤ 1) {δ : ℝ} (hq : Summable fun j => ‖q j‖ * ρ j ^ (-δ)) :
    DifferentiableOn ℂ (lowLock q ρ) {s : ℂ | s.re < 1 / 2 + δ} := by
  have hU : IsOpen {s : ℂ | s.re < 1 / 2 + δ} := isOpen_lt Complex.continuous_re continuous_const
  refine differentiableOn_tsum_of_summable_norm hq (fun j => ?_) hU (fun j s hs => ?_)
  · intro s _
    have hρ : (ρ j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hρ0 j).ne'
    exact ((differentiableAt_id.sub_const _).neg.const_cpow (Or.inl hρ)).const_mul _
      |>.differentiableWithinAt
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_lowLock_term_le (hρ0 j) (hρ1 j) hs) (norm_nonneg _)

theorem norm_lowLock_le {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ1 : ∀ j, ρ j ≤ 1)
    (hq : Summable fun j => ‖q j‖) {s : ℂ} (hs : s.re ≤ 1 / 2) :
    ‖lowLock q ρ s‖ ≤ ∑' j, ‖q j‖ := by
  have hb : ∀ j, ‖q j * (ρ j : ℂ) ^ (-(s - 1 / 2))‖ ≤ ‖q j‖ := fun j => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_lowLock_term_le_one (hρ0 j) (hρ1 j) hs)
  exact (norm_tsum_le_tsum_norm (hq.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
    (hq.of_nonneg_of_le (fun _ => norm_nonneg _) hb |>.tsum_le_tsum hb hq)

/-- On the critical line the lock is an exponential sum. -/
theorem lowLock_line (q : ℕ → ℂ) {ρ : ℕ → ℝ} (hρ0 : ∀ j, 0 < ρ j) (y : ℝ) :
    lowLock q ρ (1 / 2 - (y : ℂ) * I) = ∑' j, q j * bohrChar (-Real.log (ρ j)) y := by
  unfold lowLock bohrChar
  congr 1
  funext j
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hρ0 j).ne'),
    ← Complex.ofReal_log (hρ0 j).le]
  congr 1
  push_cast
  ring

/-- An absolutely convergent exponential sum is almost periodic. -/
theorem isBohrAlmostPeriodic_tsum_bohrChar {c : ℕ → ℂ} (hc : Summable fun j => ‖c j‖)
    (θ : ℕ → ℝ) : _root_.HTGeometry.IsBohrAlmostPeriodic fun y => ∑' j, c j * bohrChar (θ j) y := by
  refine _root_.HTGeometry.isBohrAlmostPeriodic_of_uniform_approx fun ε hε => ?_
  obtain ⟨N, hN⟩ := ((tendsto_sum_nat_add fun j => ‖c j‖).eventually (gt_mem_nhds hε)).exists
  have hap : _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun y => ∑ j ∈ Finset.range N, (fun j y => c j * bohrChar (θ j) y) j y) :=
    isBohrAlmostPeriodic_sum (Finset.range N) (F := fun j y => c j * bohrChar (θ j) y)
      (fun j _ => continuous_const.mul (continuous_bohrChar _))
      (fun j _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrChar _))
  refine ⟨_, hap, fun y => ?_⟩
  have hn : ∀ j, ‖c j * bohrChar (θ j) y‖ = ‖c j‖ := fun j => by
    rw [norm_mul, norm_bohrChar, mul_one]
  have hs : Summable fun j => c j * bohrChar (θ j) y :=
    Summable.of_norm (hc.congr fun j => (hn j).symm)
  have hsplit := hs.sum_add_tsum_nat_add N
  have he : (∑' j, c j * bohrChar (θ j) y) -
      ∑ j ∈ Finset.range N, (fun j y => c j * bohrChar (θ j) y) j y =
      ∑' j, c (j + N) * bohrChar (θ (j + N)) y := by
    rw [← hsplit]; simp
  rw [he]
  have hs' : Summable fun j => ‖c (j + N) * bohrChar (θ (j + N)) y‖ :=
    ((summable_nat_add_iff N).mpr hc).congr fun j => (hn (j + N)).symm
  refine (norm_tsum_le_tsum_norm hs').trans (le_of_eq_of_le ?_ hN.le)
  exact tsum_congr fun j => hn (j + N)

/-- **A lock with spectrum in `(0, 1]` is unimodular on the whole critical line.** -/
theorem norm_lowLock_line {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ1 : ∀ j, ρ j ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hq : Summable fun j => ‖q j‖ * ρ j ^ (-δ))
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = lowLock q ρ (lineS τ) * G (lineS τ))
    (y : ℝ) : ‖lowLock q ρ (1 / 2 - (y : ℂ) * I)‖ = 1 := by
  have hqn := summable_norm_of_lowLock hρ0 hρ1 hδ hq
  -- a globally continuous copy of the lock, equal to it on the line
  set cl : ℂ → ℂ := fun s => ((min s.re (1 / 2) : ℝ) : ℂ) + (s.im : ℂ) * I with hcl
  have hcl_re : ∀ s, (cl s).re ≤ 1 / 2 := fun s => by simp [hcl]
  have hclc : Continuous cl := by rw [hcl]; fun_prop
  have hVcont : ContinuousOn (lowLock q ρ) {s : ℂ | s.re < 1 / 2 + δ} :=
    (differentiableOn_lowLock hρ0 hρ1 hq).continuousOn
  have hVc : Continuous fun s => lowLock q ρ (cl s) :=
    hVcont.comp_continuous hclc fun s => by
      show (cl s).re < 1 / 2 + δ
      linarith [hcl_re s]
  have hcl_line : ∀ s : ℂ, s.re = 1 / 2 → cl s = s := fun s hs => by
    apply Complex.ext <;> simp [hcl, hs]
  have hlock' : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = (fun s => lowLock q ρ (cl s)) (lineS τ) * G (lineS τ) := by
    intro τ hτ
    simp only [hcl_line _ (lineS_re τ)]
    exact hlock τ hτ
  have hpos : ∀ y : ℝ, 0 < y → ‖lowLock q ρ (1 / 2 - (y : ℂ) * I)‖ = 1 := by
    intro y hy
    have h := norm_lock_eq_one hsl hΦd hΦre hid hGc hGd hG2 hVc hlock' hy
    rwa [hcl_line _ (by simp)] at h
  -- almost periodicity carries the identity to the whole line
  set f : ℝ → ℝ := fun y => ‖lowLock q ρ (1 / 2 - (y : ℂ) * I)‖ + (-1) with hf
  have hfa : _root_.HTGeometry.IsBohrAlmostPeriodic f := by
    have h := isBohrAlmostPeriodic_add_const_real (isBohrAlmostPeriodic_norm_real
      (isBohrAlmostPeriodic_tsum_bohrChar hqn fun j => -Real.log (ρ j))) (-1)
    have hfeq : f = fun t => ‖∑' j, q j * bohrChar (-Real.log (ρ j)) t‖ + -1 := by
      funext t
      simp only [hf, lowLock_line q hρ0 t]
    rw [hfeq]
    exact h
  have hf0 : Tendsto f atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [hf]
    rw [hpos y hy]
    norm_num
  have h := _root_.HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hfa hf0 y
  simp only [hf] at h
  linarith

/-- **A lock with spectrum in `(0, 1]` is contractive to the left of the critical line.** -/
theorem norm_lowLock_le_one {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ1 : ∀ j, ρ j ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hq : Summable fun j => ‖q j‖ * ρ j ^ (-δ))
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = lowLock q ρ (lineS τ) * G (lineS τ))
    {s : ℂ} (hs : s.re ≤ 1 / 2) : ‖lowLock q ρ s‖ ≤ 1 := by
  have hqn := summable_norm_of_lowLock hρ0 hρ1 hδ hq
  set B : ℝ := ∑' j, ‖q j‖ with hB
  set f : ℂ → ℂ := fun z => lowLock q ρ (1 / 2 - z) with hf
  have hfd : DifferentiableOn ℂ f {z : ℂ | -δ < z.re} := by
    have h := differentiableOn_lowLock hρ0 hρ1 hq
    refine h.comp ((differentiable_const _).sub differentiable_id).differentiableOn ?_
    intro z hz
    show (1 / 2 - z).re < 1 / 2 + δ
    have : -δ < z.re := hz
    simp; linarith
  have hfB : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ B := fun z hz =>
    norm_lowLock_le hρ0 hρ1 hqn (by simp; linarith)
  have hdiff : DiffContOnCl ℂ f {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.diffContOnCl (hfd.mono ?_)
    refine (closure_lt_subset_le continuous_const Complex.continuous_re).trans ?_
    intro z hz
    have : (0 : ℝ) ≤ z.re := hz
    show -δ < z.re
    linarith
  have hexp : ∃ c < (2 : ℝ), ∃ A,
      f =O[Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}] fun z => Real.exp (A * ‖z‖ ^ c) := by
    refine ⟨0, by norm_num, 0, IsBigO.of_bound B ?_⟩
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    have hz' : (0 : ℝ) < z.re := hz
    simpa using hfB z hz'.le
  have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖f x‖ :=
    ⟨B, Filter.eventually_map.mpr ((eventually_ge_atTop 0).mono fun x hx =>
      hfB x (by simpa using hx))⟩
  have him : ∀ x : ℝ, ‖f (x * I)‖ ≤ 1 := fun x => by
    rw [norm_lowLock_line hsl hΦd hΦre hid hGc hGd hG2 hρ0 hρ1 hδ hq hlock x]
  have h := PhragmenLindelof.right_half_plane_of_bounded_on_real hdiff hexp hre him
    (z := 1 / 2 - s) (by simp; linarith)
  simpa [hf] using h

/-- **Locks with spectrum below one force the true producer.**  Let `G` be a Herglotz producer for
the weights `lam` with lower-line lock `G(1 − s) = Σ_j q_j ρ_j^{−(s−½)} G(s)`, where
`0 < ρ_j ≤ 1` and `Σ_j |q_j| ρ_j^{−δ} < ∞` for some `δ > 0`.  Then `lam(n) = Λ(n)` for all
`n ≥ 2`, and the Riemann hypothesis holds. -/
theorem lower_spectrum_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ0 : ∀ j, 0 < ρ j) (hρ1 : ∀ j, ρ j ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hq : Summable fun j => ‖q j‖ * ρ j ^ (-δ))
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (∑' j, q j * (ρ j : ℂ) ^ (-(lineS τ - 1 / 2))) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hlock' : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = lowLock q ρ (lineS τ) * G (lineS τ) := hlock
  have hd := differentiableOn_lowLock hρ0 hρ1 hq
  refine inner_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 hδ (fun s _ hs _ => ?_)
    (fun s _ hs _ => norm_lowLock_le_one hsl hΦd hΦre hidT hGc hGd hG2 hρ0 hρ1 hδ hq hlock'
      hs.le) hlock'
  exact hd.differentiableAt
    ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds (show s.re < 1 / 2 + δ from hs))

end

end AbelianTwist

end RHTower
