import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The entropy cost of a positive fraction of Hilbert-scale gate budgets -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- The gate entropy divided by dimension is at most 32 log(2)/q in
the limit for budgets D/[q(N+1)]. The architecture and mesh contributions
are lower order in D. -/
theorem positive_budget_exponent (q : ℕ) (hq : 0 < q) (δ y b : ℝ) (hδ : 0 < δ)
    (hy : 0 < y) (hb : 0 < b) (hr : Real.log y+32*Real.log 2/q < Real.log b) :
    ∀ᶠ n : ℕ in atTop,
      let s := 2^n/(q*(n+1))
      ((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s*zeroGateArcDensity (2^n) y < b^(2^n:ℕ) := by
  have hd : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlogD := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hd
  have hlogN := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn
  have hinv := hd.inv_tendsto_atTop
  have hlim : Tendsto (fun n : ℕ => Real.log 2*((2:ℝ)^n)⁻¹ +
      2*(Real.log ((2:ℝ)^n)/(2:ℝ)^n) + (2/(q:ℝ))*(Real.log ((n:ℝ)+1)/((n:ℝ)+1)) +
      32*Real.log 2/q + (1-((2:ℝ)^n)⁻¹)*Real.log y) atTop
      (𝓝 (Real.log y+32*Real.log 2/q)) := by
    have h := ((((hinv.const_mul (Real.log 2)).add (hlogD.const_mul 2)).add
      (hlogN.const_mul (2/(q:ℝ)))).add_const (32*Real.log 2/q)).add
      ((hinv.const_sub 1).mul_const (Real.log y))
    simpa [Function.comp_def,add_comm (Real.log y)] using h
  filter_upwards [hlim.eventually_lt_const hr,hn.eventually_ge_atTop (8/δ),
    eventually_ge_atTop 1] with n hl hlarge hn1
  intro s
  let D := (2:ℝ)^n
  let N := (n:ℝ)+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hq' : 0 < (q:ℝ) := Nat.cast_pos.mpr hq
  have hd2 : 2 ≤ D := by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn1
  have hsq : (s:ℝ)*((q:ℝ)*N) ≤ D := by
    change ((2^n/(q*(n+1)):ℕ):ℝ)*((q:ℝ)*((n:ℝ)+1)) ≤ (2:ℝ)^n
    exact_mod_cast (Nat.div_mul_le_self (2^n) (q*(n+1)))
  have hsle : (s:ℝ) ≤ D := by
    have h1 : 1 ≤ (q:ℝ)*N := one_le_mul_of_one_le_of_one_le
      (by exact_mod_cast hq) (by dsimp [N]; linarith only [Nat.cast_nonneg (α := ℝ) n])
    exact (le_mul_of_one_le_right (Nat.cast_nonneg _) h1).trans hsq
  have hNmesh : 8 ≤ δ*N := by
    simpa only [mul_comm δ] using (div_le_iff₀ hδ).mp hlarge
  have hmesh : 1+4*(s:ℝ)/δ ≤ D := by
    have hq1 : 1 ≤ (q:ℝ) := by exact_mod_cast hq
    have hsN : (s:ℝ)*N ≤ D := calc
      _ ≤ (q:ℝ)*((s:ℝ)*N) := le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg s) hN.le) hq1
      _ = s*((q:ℝ)*N) := by ring
      _ ≤ D := hsq
    have hx := (mul_le_mul_of_nonneg_right hNmesh (Nat.cast_nonneg s)).trans_eq
      (by ring : δ*N*s = δ*(s*N))
    have hpay := hx.trans (mul_le_mul_of_nonneg_left hsN hδ.le)
    have hdiv : 4*(s:ℝ)/δ ≤ D/2 := (div_le_iff₀ hδ).mpr (by linarith only [hpay])
    linarith only [hdiv,hd2]
  have hsub : (s:ℝ) ≤ D/((q:ℝ)*N) := (le_div_iff₀ (mul_pos hq' hN)).mpr hsq
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by dsimp [N]; linarith only [Nat.cast_nonneg (α := ℝ) n])
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogD' : Real.log D=(n:ℝ)*Real.log 2 := Real.log_pow _ _
  have hNexp : (s:ℝ)*(2*Real.log N) ≤ D*((2/(q:ℝ))*(Real.log N/N)) := by
    apply (mul_le_mul_of_nonneg_right hsub (by positivity : 0 ≤ 2*Real.log N)).trans_eq
    ring
  have hDexp : (s:ℝ)*(32*Real.log D) ≤ D*(32*Real.log 2/q) := by
    rw [hlogD']
    have hsn : (s:ℝ)*(n:ℝ) ≤ D/q := by
      apply (le_div_iff₀ hq').mpr
      apply le_trans _ hsq
      dsimp [N]; nlinarith only [mul_nonneg (Nat.cast_nonneg s) hq'.le]
    have he := mul_le_mul_of_nonneg_right hsn (mul_nonneg (by norm_num : (0:ℝ)≤32) hlog20)
    calc
      _ = (s:ℝ)*(n:ℝ)*(32*Real.log 2) := by ring
      _ ≤ (D/(q:ℝ))*(32*Real.log 2) := he
      _ = D*(32*Real.log 2/q) := by simp only [div_eq_mul_inv]; ring
  have hDm : ((2^n-1:ℕ):ℝ)=D-1 := by
    rw [Nat.cast_sub (one_le_pow₀ (by decide)),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hUp : ((s:ℝ)+1)*(N^2*(1+4*(s:ℝ)/δ)^32)^s*zeroGateArcDensity (2^n) y ≤
      (2*D)*(N^2*D^32)^s*(D*y^(2^n-1:ℕ)) := by
    have hden : zeroGateArcDensity (2^n) y = D*y^(2^n-1:ℕ) := by
      simp only [zeroGateArcDensity,Nat.cast_pow,Nat.cast_ofNat,D]
    rw [hden]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg hD.le (pow_nonneg hy.le _))
    have htop : (s:ℝ)+1 ≤ 2*D := by linarith only [hsle,hd2]
    apply mul_le_mul htop _ (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmesh 32) (sq_nonneg N)
  apply hUp.trans_lt
  apply (Real.log_lt_log_iff (by positivity) (pow_pos hb _)).mp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) hD.ne',Real.log_pow (N^2*D^32),Real.log_mul (by positivity) (by positivity),
    Real.log_pow N,Real.log_pow D,Real.log_mul hD.ne' (pow_pos hy _).ne',Real.log_pow y,Real.log_pow b,hDm]
  push_cast
  change Real.log 2 + Real.log D + (s:ℝ)*(2*Real.log N+32*Real.log D) +
    (Real.log D+(D-1)*Real.log y) < D*Real.log b
  change Real.log 2*D⁻¹+2*(Real.log D/D)+(2/(q:ℝ))*(Real.log N/N)+32*Real.log 2/q+
    (1-D⁻¹)*Real.log y < Real.log b at hl
  have hfinal := mul_lt_mul_of_pos_left hl hD
  have heq : D*(Real.log 2*D⁻¹+2*(Real.log D/D)+(2/(q:ℝ))*(Real.log N/N)+32*Real.log 2/q+
      (1-D⁻¹)*Real.log y) = Real.log 2+2*Real.log D+D*((2/(q:ℝ))*(Real.log N/N))+
      D*(32*Real.log 2/q)+(D-1)*Real.log y := by field_simp
  rw [heq] at hfinal
  linarith only [hfinal,hNexp,hDexp]

/-- Budgets of order D/N have exponentially small long-time fractions,
with an explicit entropy penalty at the original operator tolerance. -/
theorem gaussian_hilbert_budget_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (q : ℕ), 0 < q → ∀ x ∈ Ioo (0:ℝ) (1/2),
      ∀ b : ℝ, 0 < b → Real.log x+32*Real.log 2/q < Real.log b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ j ≤ D/(q*(N+1)),
          visitFraction H j (zeroGateArcTolerance x) a T < b^D := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro q hq x hx b hb hxb
  have hcon : ContinuousAt (fun z : ℝ => Real.log z+32*Real.log 2/q) x :=
    (Real.continuousAt_log hx.1.ne').add continuousAt_const
  have hynear := (hcon.eventually_lt_const hxb).and (eventually_lt_nhds hx.2)
  have hyr : ∀ᶠ y in 𝓝[>] x, Real.log y + 32*Real.log 2/q < Real.log b ∧ y < 1/2 :=
    hynear.filter_mono nhdsWithin_le_nhds
  have hright : ∀ᶠ y in 𝓝[>] x, x < y := self_mem_nhdsWithin
  obtain ⟨y,hxy,hyb,hyhalf⟩ := (hright.and hyr).exists
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
  have hδ : 0 < δ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance ⟨hx.1.le,hx.2.le⟩
    ⟨(hx.1.trans hxy).le,hyhalf.le⟩ hxy)
  filter_upwards [(tendsto_add_atTop_nat 3).eventually (positive_budget_exponent q hq δ y b hδ
    (hx.1.trans hxy) hb hyb)] with k he
  intro N D H a
  have hu := finite_budget_eventually_lt H (hω k) (D/(q*(N+1))) hx.1.le hxy hyhalf a (b^D) he
  filter_upwards [hu,eventually_gt_atTop a] with T ht hT j hj
  exact (visitFraction_mono H hj _ a T hT.le).trans_lt ht

#print axioms gaussian_hilbert_budget_occupation
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
