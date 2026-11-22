import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.HalfTurn
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.RegularBonds
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Unit lower gate density up to a prefix-independent short time -/
open Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section

private theorem small_window (M a : ℝ) : ∃ b : ℝ, 0<b ∧ ∀ t∈Set.Icc 0 b,
    t*M ≤ 1/100 ∧ M^2*t*(a+t) ≤ 1/1000000 := by
  have h₁ : Continuous (fun t : ℝ => t*M) := continuous_id.mul_const _
  have h₂ : Continuous (fun t : ℝ => M^2*t*(a+t)) := (continuous_const.mul continuous_id).mul (continuous_const.add continuous_id)
  have h : ∀ᶠ t : ℝ in 𝓝 0, t*M < 1/100 :=
    h₁.continuousAt.tendsto.eventually_lt_const (by norm_num)
  have k : ∀ᶠ t : ℝ in 𝓝 0, M^2*t*(a+t) < 1/1000000 :=
    h₂.continuousAt.tendsto.eventually_lt_const (by norm_num)
  obtain ⟨d,hd,hr⟩ := Metric.eventually_nhds_iff.mp (h.and k)
  refine ⟨d/2,half_pos hd,fun t ht => ?_⟩
  have he := hr (y:=t) (by rw [Real.dist_eq,sub_zero,abs_of_nonneg ht.1]; exact ht.2.trans_lt (half_lt_self hd))
  exact ⟨he.1.le,he.2.le⟩

private theorem crossed_bound {n : ℕ} (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (t M q a : ℝ) (ht : 0<t) (hM : 0≤M) (hq : 0<q) (ha : a=π/(2*q))
    (hlate : a/q ≤ t*(n+1:ℕ)) (hs : t*M≤1/100) (hv : M^2*t*(a+t)≤1/1000000)
    (G : Finset (Fin (n+1))) (hG : G ⊆ crossed c) (hsize : ((crossed c).card:ℝ) ≤ G.card+7*q*(n+1:ℕ))
    (hgood : ∀ e∈G, q/2 ≤ |u (zz e)| ∧ localMass u e≤M^2) (z : ℂ) (hz : ‖z‖=1)
    (hfit : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ ≤ 1/4) :
    ((crossed c).card:ℝ) ≤ 8*q*(n+1:ℕ) := by
  by_contra! hh
  have ha' : 0<a := ha ▸ div_pos pi_pos (mul_pos two_pos hq)
  have hcard : q*(n+1:ℕ) ≤ G.card := by linarith only [hh,hsize]
  have hreach : a/t ≤ (G.card:ℝ) := by
    apply (div_le_iff₀ ht).mpr
    have hl := (div_le_iff₀ hq).mp hlate
    linarith only [hl,mul_le_mul_of_nonneg_right hcard ht.le]
  obtain ⟨Q,hQ,hcq⟩ := Finset.exists_subset_card_eq (Nat.ceil_le.mpr hreach)
  have hct : a ≤ Q.card*t := (div_le_iff₀ ht).mp (by rw [hcq]; exact Nat.le_ceil _)
  have hct' : (Q.card:ℝ)*t ≤ a+t := by
    have h := Nat.ceil_lt_add_one (div_nonneg ha'.le ht.le)
    rw [hcq]
    calc _ ≤ (a/t+1)*t := mul_le_mul_of_nonneg_right h.le ht.le
         _ = _ := by field_simp
  have hvar : (Q.card:ℝ)*M^2*t^2 ≤ 1/1000000 := by
    apply le_trans _ hv
    nlinarith only [mul_le_mul_of_nonneg_left hct' (mul_nonneg (sq_nonneg M) ht.le)]
  have hsum : Q.card*(q/2) ≤ ∑ e∈Q, |u (zz e)| := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s:=Q) (fun e he => (hgood e (hQ he)).1)
  have hmass : π ≤ 4*t*∑ e∈Q, |u (zz e)| := by
    have he := (eq_div_iff (ne_of_gt (mul_pos two_pos hq))).mp ha
    nlinarith only [he,mul_le_mul_of_nonneg_left hct hq.le,mul_le_mul_of_nonneg_left hsum ht.le]
  exact (no_cut_fit u C c Q (hQ.trans hG) M t hM ht (fun e he => (hgood e (hQ he)).2) hmass hs hvar z hz).not_ge hfit

/-- At every accuracy at most 1/4 the cost on [A/N,b] exceeds any fixed
fraction below one gate per bond. Both constants are independent of N. -/
theorem gaussian_physical_window : ∀ η : ℝ, 0<η → ∃ A b : ℝ, 0<A ∧ 0<b ∧
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, A ≤ |t| *(n+1:ℕ) → |t| ≤ b →
      ∀ s : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) s (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        (1-η)*(n+1:ℕ) < (s:ℝ) := by
  obtain ⟨B,hB,hm⟩ := gaussian_regular_bonds
  intro η hη
  obtain ⟨k,hk⟩ := exists_nat_gt (16/η)
  let q : ℝ := 1/(k+1:ℕ)
  have hq : 0<q := by dsimp only [q]; positivity
  have hqsmall : 16*q<η := by
    have h := (div_lt_iff₀ hη).mp hk
    dsimp only [q]
    push_cast
    field_simp
    linarith only [h,hη]
  let M := sqrt (B/q)
  have hM : 0≤M := sqrt_nonneg _
  have hM₂ : M^2=B/q := sq_sqrt (div_nonneg hB.le hq.le)
  let a := π/(2*q)
  have ha : 0<a := div_pos pi_pos (mul_pos two_pos hq)
  obtain ⟨b,hb,hs⟩ := small_window M a
  refine ⟨a/q,b,div_pos ha hq,hb,?_⟩
  filter_upwards [hm] with ω hω
  filter_upwards [hω k] with n hn
  intro t hlate hshort s hfit
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Register (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
  have ht : 0<|t| := by
    apply lt_of_le_of_ne (abs_nonneg _) (fun h => ?_)
    rw [←h,zero_mul] at hlate; exact (div_pos ha hq).not_ge hlate
  have hpos : HasProjectiveCircuitApproximation (n+2) (1/4) s (unitaryEvolution H.val |t|) := by
    by_cases h : 0≤t
    · rwa [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; exact hfit.neg_time H
  obtain ⟨z,hz,C,hC,he⟩ := hpos
  obtain ⟨c,hcut⟩ := many_crossed C
  obtain ⟨G,hG,hsize,hgood⟩ := hn (crossed c)
  have hh := hs |t| ⟨ht.le,hshort⟩
  have hx := crossed_bound u C c |t| M q a ht hM hq rfl hlate hh.1 hh.2 G hG hsize
    (fun e he => ⟨(hgood e he).1,hM₂ ▸ (hgood e he).2⟩) z hz he
  have hcut' : ((n+1:ℕ):ℝ) ≤ (s:ℝ)+2*(crossed c).card := by exact_mod_cast hcut.trans (Nat.add_le_add_right hC _)
  linarith only [hcut',hx,mul_lt_mul_of_pos_right hqsmall (show 0<((n+1:ℕ):ℝ) by positivity)]

#print axioms gaussian_physical_window
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
