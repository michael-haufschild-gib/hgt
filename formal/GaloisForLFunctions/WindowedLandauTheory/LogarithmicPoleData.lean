import Mathlib
import GaloisForLFunctions.HTGeometry.LogDerivZeroPole

/-!
# Pole data of normalized logarithmic derivatives

For an entire function `P` with `P(1) ≠ 0` and a constant `κ` let

```text
Φ_P(s) = -(P'/P(s) - s·P'/P(1) + κ(1 - s)) / (s(s - 1)).
```

The numerator vanishes at `s = 1`, so `Φ_P` extends holomorphically there; `logPoleFun` is that
extension, written with `dslope`. Off `0` it is holomorphic wherever `P ≠ 0`, and at a zero
`ρ ∉ {0, 1}` of order `m` it has a simple pole with residue `m / (ρ(1 - ρ))`
(`exists_logPoleFun_principal`); positive combinations add the residues
(`exists_sum_logPoleFun_principal`). With `P = L(χ, ·)`, `κ = 0`, or `P(s) = (s - 1)ζ(s)`, `κ = 1`,
`Φ_P` is the Mellin transform of the Cesàro–Chebyshev ramp.
-/

open Complex Filter Topology Set

namespace WindowedLandauTheory

noncomputable section

/-- The numerator `-(P'/P(s) - s·P'/P(1) + κ(1 - s))`; it vanishes at `s = 1`. -/
def logPoleNum (P : ℂ → ℂ) (κ : ℂ) (s : ℂ) : ℂ :=
  -(logDeriv P s - s * logDeriv P 1 + κ * (1 - s))

/-- `Φ_P(s) = logPoleNum P κ s / (s(s - 1))`, with the removable singularity at `s = 1` filled. -/
def logPoleFun (P : ℂ → ℂ) (κ : ℂ) (s : ℂ) : ℂ := dslope (logPoleNum P κ) 1 s / s

theorem logPoleNum_one (P : ℂ → ℂ) (κ : ℂ) : logPoleNum P κ 1 = 0 := by
  simp [logPoleNum]

theorem logPoleFun_eq (P : ℂ → ℂ) (κ : ℂ) {s : ℂ} (hs : s ≠ 1) :
    logPoleFun P κ s = logPoleNum P κ s / (s * (s - 1)) := by
  rw [logPoleFun, dslope_of_ne _ hs, slope_def_field, logPoleNum_one, sub_zero, div_div,
    mul_comm (s - 1) s]

theorem differentiableOn_logPoleNum {P : ℂ → ℂ} (hP : Differentiable ℂ P) (κ : ℂ) :
    DifferentiableOn ℂ (logPoleNum P κ) {s | P s ≠ 0} := by
  intro s hs
  have hPd : DifferentiableAt ℂ (deriv P) s := (hP.analyticAt s).deriv.differentiableAt
  have hd : DifferentiableAt ℂ (fun t => deriv P t / P t) s := hPd.div (hP s) hs
  have h1 : DifferentiableAt ℂ (fun t : ℂ => t * logDeriv P 1) s := by fun_prop
  have h2 : DifferentiableAt ℂ (fun t : ℂ => κ * (1 - t)) s := by fun_prop
  have h : DifferentiableAt ℂ (logPoleNum P κ) s := by
    have e : logPoleNum P κ = fun t => -(deriv P t / P t - t * logDeriv P 1 + κ * (1 - t)) :=
      funext fun t => by rw [logPoleNum, logDeriv_apply]
    rw [e]
    exact ((hd.sub h1).add h2).neg
  exact h.differentiableWithinAt

/-- `Φ_P` is holomorphic off `0` and the zeros of `P`. -/
theorem differentiableOn_logPoleFun {P : ℂ → ℂ} (hP : Differentiable ℂ P) (hP1 : P 1 ≠ 0)
    (κ : ℂ) : DifferentiableOn ℂ (logPoleFun P κ) ({s | P s ≠ 0} \ {0}) := by
  have hU : IsOpen {s : ℂ | P s ≠ 0} := isOpen_ne_fun hP.continuous continuous_const
  have hd : DifferentiableOn ℂ (dslope (logPoleNum P κ) 1) {s | P s ≠ 0} :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hP1)).mpr (differentiableOn_logPoleNum hP κ)
  exact (hd.mono fun _ h => h.1).div differentiableOn_id fun s hs => hs.2

/-- **Principal part at a zero.** At `ρ ∉ {0, 1}`, `Φ_P = (m/(ρ(1-ρ)))/(s-ρ) + h` with `h` analytic,
where `m` is the order of `P` at `ρ` (so `m > 0` exactly when `P(ρ) = 0`). The residue comes from
`P'/P = m/(s-ρ) + Q'/Q` for `P = (s-ρ)^m Q` and
`-1/(s(s-1)) = 1/(ρ(1-ρ)) + O(s-ρ)`. -/
theorem exists_logPoleFun_principal {P : ℂ → ℂ} (hP : Differentiable ℂ P) (hP1 : P 1 ≠ 0)
    (κ : ℂ) {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    ∃ m : ℕ, (P ρ = 0 ↔ 0 < m) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, logPoleFun P κ s = ((m : ℂ) / (ρ * (1 - ρ))) / (s - ρ) + h s := by
  by_cases hPρ : P ρ = 0
  · -- a zero of finite order `k + 1`
    have hPa : AnalyticOnNhd ℂ P univ := hP.differentiableOn.analyticOnNhd isOpen_univ
    have hord : analyticOrderAt P ρ ≠ ⊤ :=
      hPa.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 1)
        (mem_univ ρ) (by rw [analyticOrderAt_eq_zero.mpr (Or.inr hP1)]; exact ENat.zero_ne_top)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hord
    obtain ⟨Q, hQa, hQρ, hfac⟩ := (hP.analyticAt ρ).analyticOrderAt_eq_natCast.mp hn.symm
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h0 : P ρ = (ρ - ρ) ^ 0 • Q ρ := hfac.self_of_nhds
      rw [pow_zero, one_smul] at h0
      exact hQρ (by rw [← h0]; exact hPρ)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn0
    have hlog := GaloisForLFunctions.HTGeometry.logDeriv_eventuallyEq_of_factor (f := P) (n := k)
      hQa hQρ (hfac.mono fun z hz => hz.trans (smul_eq_mul _ _))
    have hden : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
    have hden' : ρ * (ρ - 1) * (ρ * (ρ - 1)) ≠ 0 := mul_ne_zero hden hden
    refine ⟨k + 1, ⟨fun _ => Nat.succ_pos k, fun _ => hPρ⟩,
      fun s => -(logDeriv Q s - s * logDeriv P 1 + κ * (1 - s)) / (s * (s - 1)) +
        ((k + 1 : ℕ) : ℂ) * (s + ρ - 1) / (ρ * (ρ - 1) * (s * (s - 1))), ?_, ?_⟩
    · have hL : AnalyticAt ℂ (logDeriv Q) ρ := by
        have e : logDeriv Q = fun s => deriv Q s / Q s := funext fun s => logDeriv_apply Q s
        rw [e]
        exact hQa.deriv.div hQa hQρ
      have h1 : AnalyticAt ℂ (fun s : ℂ => s * logDeriv P 1) ρ := by fun_prop
      have h2 : AnalyticAt ℂ (fun s : ℂ => κ * (1 - s)) ρ := by fun_prop
      have hN : AnalyticAt ℂ (fun s : ℂ => -(logDeriv Q s - s * logDeriv P 1 + κ * (1 - s))) ρ :=
        ((hL.sub h1).add h2).neg
      have hD : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) ρ := by fun_prop
      have hT : AnalyticAt ℂ (fun s : ℂ => ((k + 1 : ℕ) : ℂ) * (s + ρ - 1)) ρ := by fun_prop
      have hD' : AnalyticAt ℂ (fun s : ℂ => ρ * (ρ - 1) * (s * (s - 1))) ρ := by fun_prop
      exact (hN.div hD hden).add (hT.div hD' hden')
    · filter_upwards [hlog, self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hρ0),
        nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hρ1)] with s hs hsρ hs0 hs1
      have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
      have hs0' : s ≠ 0 := hs0
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
      have hρ1'' : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
      rw [logPoleFun_eq P κ hs1, logPoleNum, hs]
      push_cast
      field_simp
      ring
  · refine ⟨0, ⟨fun h => absurd h hPρ, fun h => absurd h (lt_irrefl 0)⟩, logPoleFun P κ, ?_, ?_⟩
    · have hopen : IsOpen ({s : ℂ | P s ≠ 0} \ {0}) :=
        (isOpen_ne_fun hP.continuous continuous_const).sdiff isClosed_singleton
      exact (differentiableOn_logPoleFun hP hP1 κ).analyticAt (hopen.mem_nhds ⟨hPρ, hρ0⟩)
    · exact Eventually.of_forall fun s => by simp

/-- **Pole data of a positive combination.** For entire `P_j` with `P_j(1) ≠ 0` and real weights
`w_j`, the combination `Σ w_j Φ_{P_j}` has at `ρ ∉ {0, 1}` the principal part
`(Σ w_j m_j)/(ρ(1-ρ)) / (s-ρ)`, where `m_j > 0` exactly when `P_j(ρ) = 0`. -/
theorem exists_sum_logPoleFun_principal {ι : Type*} (S : Finset ι) {P : ι → ℂ → ℂ}
    (hP : ∀ j, Differentiable ℂ (P j)) (hP1 : ∀ j, P j 1 ≠ 0) (κ : ι → ℂ) (w : ι → ℝ) {ρ : ℂ}
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    ∃ m : ι → ℕ, (∀ j, P j ρ = 0 ↔ 0 < m j) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, ∑ j ∈ S, (w j : ℂ) * logPoleFun (P j) (κ j) s =
        (((∑ j ∈ S, w j * m j : ℝ) : ℂ) / (ρ * (1 - ρ))) / (s - ρ) + h s := by
  choose m hm h hh hev using fun j => exists_logPoleFun_principal (hP j) (hP1 j) (κ j) hρ0 hρ1
  have han : AnalyticAt ℂ (fun s => ∑ j ∈ S, (w j : ℂ) * h j s) ρ := by
    have := Finset.analyticAt_sum S (f := fun j s => (w j : ℂ) * h j s)
      fun j _ => analyticAt_const.mul (hh j)
    rwa [Finset.sum_fn] at this
  refine ⟨m, hm, fun s => ∑ j ∈ S, (w j : ℂ) * h j s, han, ?_⟩
  filter_upwards [(Filter.eventually_all_finset S).mpr fun j _ => hev j] with s hs
  rw [Finset.sum_congr rfl fun j hj => by rw [hs j hj]]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

end

end WindowedLandauTheory
