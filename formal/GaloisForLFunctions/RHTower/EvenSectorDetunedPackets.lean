import GaloisForLFunctions.RHTower.EvenSectorDetunedReflection

/-!
# Reflected packets with exact arithmetic cancellation

The two reflected copies retain the original multiplicative autocorrelation.
All cross interactions between the copies vanish at every integer logarithmic
node, including the origin. Coefficients may have either sign.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section
namespace RHTower.EvenSector.Detuned

private theorem weilTest_finite_translates {ι : Type*} {S : Finset ι}
    {c : ι → ℂ} {x : ι → ℝ} {g : ℝ → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (y : ℝ) :
    EF.weilTest (fun u => ∑ m ∈ S, c m * g (u - x m))
      (fun u => ∑ m ∈ S, c m * g (u - x m)) y =
      ∑ m ∈ S, ∑ k ∈ S, c m * conj (c k) * EF.weilTest g g (y - x m + x k) := by
  rw [weilTest_apply]
  have hpt : ∀ t : ℝ,
      (∑ m ∈ S, c m * g (t - x m)) * conj (∑ k ∈ S, c k * g (t - y - x k)) =
      ∑ m ∈ S, ∑ k ∈ S,
        c m * conj (c k) * (g (t - x m) * conj (g (t - y - x k))) := by
    intro t
    rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by
      rw [map_mul]
      ring
  have hint : ∀ m k : ι,
      Integrable fun t : ℝ => g (t - x m) * conj (g (t - y - x k)) := by
    intro m k
    exact ((hg.comp (continuous_id.sub continuous_const)).mul
      (continuous_conj.comp (hg.comp ((continuous_id.sub continuous_const).sub continuous_const))))
      .integrable_of_hasCompactSupport
        (hgc.comp_homeomorph (Homeomorph.subRight (x m))).mul_right
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ => (hint m k).const_mul _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun k _ => (hint m k).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [weilTest_apply]
  rw [← integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => g (t - x m) * conj (g (t - y - x k))) (x m)]
  congr 1
  funext t
  congr 3 <;> ring

def signs (N : ℕ) : Finset (Fin 2 × ℕ) := Finset.univ.product (Finset.Icc 1 N)

def signedCenter (N : ℕ) (p : Fin 2 × ℕ) : ℝ :=
  ![center N p.2, -center N p.2] p.1

def packet (N : ℕ) (c : ℕ → ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ p ∈ signs N, (c p.2 : ℂ) * g (u - signedCenter N p)

theorem packet_eq (N : ℕ) (c : ℕ → ℝ) (g : ℝ → ℂ) (u : ℝ) :
    packet N c g u =
      (∑ m ∈ Finset.Icc 1 N, (c m : ℂ) * g (u - center N m)) +
      ∑ m ∈ Finset.Icc 1 N, (c m : ℂ) * g (u + center N m) := by
  simp [packet, signs, signedCenter, Finset.sum_product, Fin.sum_univ_two]

theorem packet_neg {N : ℕ} {c : ℕ → ℝ} {g : ℝ → ℂ}
    (hg : ∀ u, g (-u) = g u) (u : ℝ) : packet N c g (-u) = packet N c g u := by
  have h1 : ∀ m, -u - center N m = -(u + center N m) := fun _ => by ring
  have h2 : ∀ m, -u + center N m = -(u - center N m) := fun _ => by ring
  simp only [packet_eq, h1, h2, hg]
  exact add_comm _ _

theorem contDiff_packet {N : ℕ} {c : ℕ → ℝ} {g : ℝ → ℂ} {k : ℕ}
    (hg : ContDiff ℝ k g) : ContDiff ℝ k (packet N c g) := by
  unfold packet
  exact ContDiff.sum fun p _ => contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_packet {N : ℕ} {c : ℕ → ℝ} {g : ℝ → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (packet N c g) := by
  have h : ∀ (s : Finset (Fin 2 × ℕ)),
      HasCompactSupport fun u => ∑ p ∈ s, (c p.2 : ℂ) * g (u - signedCenter N p) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℂ))
    | insert p s hp ih =>
      simp only [Finset.sum_insert hp]
      exact ((hg.comp_homeomorph (Homeomorph.subRight (signedCenter N p))).mul_left).add ih
  exact h (signs N)

theorem deriv_packet {N : ℕ} {c : ℕ → ℝ} {g : ℝ → ℂ}
    (hg : Differentiable ℝ g) : deriv (packet N c g) = packet N c (deriv g) := by
  funext u
  have h : HasDerivAt (packet N c g) (packet N c (deriv g) u) u := by
    unfold packet
    apply HasDerivAt.fun_sum
    intro p _
    have hshift := (hg (u - signedCenter N p)).hasDerivAt.comp u
      ((hasDerivAt_id u).sub_const (signedCenter N p))
    simpa using hshift.const_mul (c p.2 : ℂ)
  exact h.deriv

theorem paperFT_packet {N : ℕ} {c : ℕ → ℝ} {g : ℝ → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (packet N c g) z =
      (∑ p ∈ signs N, (c p.2 : ℂ) * Complex.exp (I * z * signedCenter N p)) * paperFT g z :=
  paperFT_sum_translate (signs N) (fun p => (c p.2 : ℂ)) (signedCenter N) hg hgc z

/-- Exact removal of the reflected interactions, before applying any positivity. -/
theorem weilTest_packet_of_reflected_zero {N : ℕ} {c : ℕ → ℝ} {g : ℝ → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (y : ℝ)
    (hzminus : ∀ m ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      EF.weilTest g g (y - (center N m + center N k)) = 0)
    (hzplus : ∀ m ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      EF.weilTest g g (y + (center N m + center N k)) = 0) :
    EF.weilTest (packet N c g) (packet N c g) y =
      2 * EF.weilTest
        (fun u => ∑ m ∈ Finset.Icc 1 N, (c m : ℂ) * g (u - resPt N m))
        (fun u => ∑ m ∈ Finset.Icc 1 N, (c m : ℂ) * g (u - resPt N m)) y := by
  let K := EF.weilTest g g
  have heq : EF.weilTest (packet N c g) (packet N c g) y =
      ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (c m : ℂ) * (c k : ℂ) *
          (K (y - center N m + center N k) + K (y - center N m - center N k) +
           K (y + center N m + center N k) + K (y + center N m - center N k)) := by
    unfold packet
    rw [weilTest_finite_translates hg hgc]
    simp only [signs, Finset.sum_product, signedCenter, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add, add_neg_eq_sub,
      Complex.conj_ofReal]
    simp only [Finset.sum_add_distrib, mul_add]
    ring
  rw [heq]
  have hpt : ∀ m ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      K (y - center N m - center N k) = 0 ∧ K (y + center N m + center N k) = 0 := by
    intro m hm k hk
    constructor
    · exact (congrArg K (by ring : y - center N m - center N k =
        y - (center N m + center N k))).trans (hzminus m hm k hk)
    · exact (congrArg K (by ring : y + center N m + center N k =
        y + (center N m + center N k))).trans (hzplus m hm k hk)
  simp_rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun k hk => by
    rw [(hpt m hm k hk).1, (hpt m hm k hk).2, add_zero, add_zero]]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hswap : (∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      (c m : ℂ) * (c k : ℂ) * K (y + center N m - center N k)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (c m : ℂ) * (c k : ℂ) * K (y - center N m + center N k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    rw [show y + center N k - center N m = y - center N m + center N k by ring]
    ring
  rw [hswap, ← two_mul, weilTest_sum_translates hg hgc]
  congr 1
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_ofReal]
  congr 2
  simp only [center, resPt]
  ring

/-- The reflected packet has exactly twice the original arithmetic correlation. -/
theorem weilTest_packet_log {N : ℕ} (hN : 1 ≤ N) {c : ℕ → ℝ} {g : ℝ → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hvan : ∀ y, width N ≤ |y| → EF.weilTest g g y = 0)
    (hc : ∀ m, N < m → c m = 0) {n : ℕ} (hn : 1 ≤ n) :
    EF.weilTest (packet N c g) (packet N c g) (Real.log n) =
      2 * EF.weilTest g g 0 * ((∑ m ∈ Finset.Icc 1 N, c (n * m) * c m : ℝ) : ℂ) := by
  rw [weilTest_packet_of_reflected_zero hg hgc (Real.log n)
    (fun m hm k hk => hvan _ (reflected_log_gap (Finset.mem_Icc.mp hm).1
      (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2 hn))
    (fun m hm k hk => hvan _ (reflected_sum_gap (Finset.mem_Icc.mp hm).1
      (Finset.mem_Icc.mp hm).2 (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2))]
  rw [weilTest_translates_log hg hgc
    (fun y hy => hvan y ((width_le_integer_gap hN).trans hy))
    (fun m hm => by rw [hc m hm, Complex.ofReal_zero]) hn]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  ring

theorem weilTest_packet_neg_log {N : ℕ} (hN : 1 ≤ N) {c : ℕ → ℝ} {g : ℝ → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hvan : ∀ y, width N ≤ |y| → EF.weilTest g g y = 0)
    (hc : ∀ m, N < m → c m = 0) {n : ℕ} (hn : 1 ≤ n) :
    EF.weilTest (packet N c g) (packet N c g) (-Real.log n) =
      2 * EF.weilTest g g 0 * ((∑ m ∈ Finset.Icc 1 N, c (n * m) * c m : ℝ) : ℂ) := by
  have hzminus : ∀ m ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      EF.weilTest g g (-Real.log n - (center N m + center N k)) = 0 := by
    intro m hm k hk
    apply hvan
    rw [show -Real.log n - (center N m + center N k) =
      -(Real.log n + (center N m + center N k)) by ring, abs_neg]
    exact reflected_sum_gap (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
      (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  have hzplus : ∀ m ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
      EF.weilTest g g (-Real.log n + (center N m + center N k)) = 0 := by
    intro m hm k hk
    apply hvan
    rw [show -Real.log n + (center N m + center N k) =
      -(Real.log n - (center N m + center N k)) by ring, abs_neg]
    exact reflected_log_gap (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
      (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2 hn
  rw [weilTest_packet_of_reflected_zero hg hgc _ hzminus hzplus,
    weilTest_translates_neg_log hg hgc
      (fun y hy => hvan y ((width_le_integer_gap hN).trans hy))
      (fun m hm => by rw [hc m hm, Complex.ofReal_zero]) hn,
    sum_conj_swap]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  ring

theorem signedCenter_abs (N : ℕ) (p : Fin 2 × ℕ) :
    |signedCenter N p| = center N p.2 := by
  rcases p with ⟨i, m⟩
  fin_cases i <;> simp [signedCenter, abs_of_pos (center_pos N m)]

theorem packet_eq_zero {N : ℕ} {c : ℕ → ℝ} {g : ℝ → ℂ} {r : ℝ}
    (hg : ∀ u, r < |u| → g u = 0) {u : ℝ}
    (hu : Real.log N + shift N + r < |u|) : packet N c g u = 0 := by
  unfold packet
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hm, hmN⟩ := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
  have hlog : Real.log p.2 ≤ Real.log N := Real.log_le_log
    (by exact_mod_cast (show 0 < p.2 by omega)) (by exact_mod_cast hmN)
  have hgap := abs_sub_abs_le_abs_sub u (signedCenter N p)
  rw [signedCenter_abs] at hgap
  rw [hg _ (by unfold center at hgap; linarith), mul_zero]

theorem packet_tsupport {N : ℕ} {c : ℕ → ℝ} {g : ℝ → ℂ} {r : ℝ}
    (hg : ∀ u, r < |u| → g u = 0) :
    tsupport (packet N c g) ⊆
      Icc (-(Real.log N + shift N + r)) (Real.log N + shift N + r) :=
  tsupport_subset_of_vanish fun _ hu => packet_eq_zero hg hu

end RHTower.EvenSector.Detuned
end
