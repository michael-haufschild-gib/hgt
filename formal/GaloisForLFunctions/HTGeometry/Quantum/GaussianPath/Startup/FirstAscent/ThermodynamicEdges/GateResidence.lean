import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Density
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.DeepResidence

/-! # Thermodynamic residence time for sublinear physical circuits -/

open Filter Set Real MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
open AfterScalar SharpOccupation ReturnSpacing.PhysicalComponents
noncomputable section

/-- Affordable forward lags in a window of length b at physical error 1/10. -/
def affordableLags {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (v b : ℝ) :=
  {t ∈ Icc (0:ℝ) b | v+t ∈ visitSet H s (1/10)}

private theorem correction_le {s N : ℝ} (hs : 0<s) (hN : 0<N) (hle : s≤N) :
    N*(s*sqrt (log (N/s))/N^2) ≤ sqrt (s/N) := by
  have hlog := log_nonneg ((one_le_div hs).mpr hle)
  have hu : log (N/s) ≤ N/s := (log_le_sub_one_of_pos (div_pos hN hs)).trans (sub_le_self _ zero_le_one)
  apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp
  rw [show N*(s*sqrt (log (N/s))/N^2)=s/N*sqrt (log (N/s)) by field_simp, mul_pow,
    sq_sqrt hlog,sq_sqrt (div_nonneg hs.le hN.le)]
  exact (mul_le_mul_of_nonneg_left hu (sq_nonneg (s/N))).trans_eq (by field_simp)

private theorem budget_eventually {s : ℕ→ℕ} {M : ℕ} (hM : 0<M)
    (hs : Tendsto (fun n : ℕ => (s n : ℝ)/((n+2 : ℕ) : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, M*s n ≤ n+2 := by
  have hm : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  filter_upwards [hs.eventually_lt_const (one_div_pos.mpr hm)] with n hn
  have hN : 0<((n+2 : ℕ) : ℝ) := by positivity
  have hb := (div_lt_div_iff₀ hN hm).mp hn
  rw [one_mul,mul_comm] at hb
  exact_mod_cast hb.le

/-- The first loss of fit, last fit and total affordable duration all
have the same limiting scaled lag at sublinear positive budgets.
The visits and budgets may be selected on the observed Gaussian chain. -/
theorem gaussian_sublinear_residence :
    ∃ w b : ℝ, 0<w ∧ 0<b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      Tendsto (fun n : ℕ => physicalWidth ω n/((n+2 : ℕ) : ℝ)) atTop (𝓝 w) ∧
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      ∀ (s : ℕ→ℕ) (v : ℕ→ℝ), (∀ᶠ n in atTop, 0<s n) →
        Tendsto (fun n : ℕ => (s n : ℝ)/((n+2 : ℕ) : ℝ)) atTop (𝓝 0) →
        (∀ᶠ n in atTop, HasProjectiveCircuitApproximation (n+2) (1/((n+2 : ℕ):ℝ)^2) 0
          (unitaryEvolution (H n).val (v n))) →
        let N := fun n : ℕ => ((n+2 : ℕ) : ℝ)
        let S := fun n => affordableLags (H n) (s n) (v n) b
        let a := 4*arcsin (1/20)/w
        Tendsto (fun n => N n*exitLag (H n) (s n) (v n)) atTop (𝓝 a) ∧
        Tendsto (fun n => N n*sSup (S n)) atTop (𝓝 a) ∧
        Tendsto (fun n => N n*volume.real (S n)) atTop (𝓝 a) := by
  obtain ⟨w,hw,_,hd⟩ := gaussian_energy_density
  obtain ⟨b,c,C,M,hb,hc,hC,hM,hr⟩ := gaussian_deep_residence
  obtain ⟨f,F,J,hf,hF,hJ,he⟩ := gaussian_deep_return_exit
  refine ⟨w,b,hw,hb,?_⟩
  filter_upwards [hd,hr,he] with ω hd hr he
  refine ⟨hd,?_⟩
  intro H s v hpos hs hv N S a
  let θ := 4*arcsin (1/20)
  let τ := fun n => θ/physicalWidth ω n
  let q := fun n => (s n : ℝ)*sqrt (log (N n/s n))/(N n)^2
  have ht : Tendsto (fun n => N n*τ n) atTop (𝓝 a) := by
    apply ((tendsto_const_nhds (x:=θ)).div hd hw.ne').congr
    intro n
    change θ/(physicalWidth ω n/N n)=N n*(θ/physicalWidth ω n)
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  have hq : Tendsto (fun n => N n*q n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa only [sqrt_zero] using hs.sqrt)
    · filter_upwards with n
      dsimp only [N,q]
      positivity
    · filter_upwards [hpos,budget_eventually hM hs] with n hp hn
      exact correction_le (Nat.cast_pos.mpr hp) (by dsimp only [N]; positivity)
        (by dsimp only [N]; exact_mod_cast (Nat.le_mul_of_pos_left (s n) hM).trans hn)
  have squeeze (x : ℕ→ℝ) (d D : ℝ) (hl : 0≤d)
      (hx : ∀ᶠ n in atTop, x n-τ n ∈ Icc (d*q n) (D*q n)) :
      Tendsto (fun n => N n*x n) atTop (𝓝 a) := by
    have hu : Tendsto (fun n => N n*τ n+D*(N n*q n)) atTop (𝓝 a) := by
      simpa only [mul_zero,add_zero] using ht.add (hq.const_mul D)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ht hu
    · filter_upwards [hx] with n hn
      have hnq : 0≤q n := by dsimp only [q,N]; positivity
      exact mul_le_mul_of_nonneg_left (sub_nonneg.mp ((mul_nonneg hl hnq).trans hn.1))
        (by dsimp only [N]; positivity)
    · filter_upwards [hx] with n hn
      have h := mul_le_mul_of_nonneg_left hn.2 (show 0≤N n by dsimp only [N]; positivity)
      linarith only [h]
  have hex := squeeze (fun n => exitLag (H n) (s n) (v n)) f F hf.le (by
    filter_upwards [he,hv,hpos,budget_eventually hJ hs] with n hn hvisit hp hm
    exact hn (v n) hvisit (s n) hp hm)
  have hsr : ∀ᶠ n in atTop, sSup (S n)-τ n ∈ Icc (c*q n) (C*q n) ∧
      volume.real (S n)-τ n ∈ Icc (c*q n) (C*q n) := by
    filter_upwards [hr,hv,hpos,budget_eventually hM hs] with n hn hvisit hp hm
    exact (hn (v n) hvisit (s n) hp hm).2.2.2
  exact ⟨hex,squeeze _ c C hc.le (hsr.mono fun _ h => h.1),
    squeeze _ c C hc.le (hsr.mono fun _ h => h.2)⟩

#print axioms gaussian_sublinear_residence
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
