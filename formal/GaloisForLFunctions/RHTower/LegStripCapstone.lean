/-
# The strip residue's shell-sum interchange: the literal single limit `(A−B)/i → Φ(c)`

The per-shell balance `tendsto_shellDiff` gives, for each `n ≥ 1`, that the `n`-th shell of the
physical field's ahead-minus-behind excess converges to `2/((cn)² − 1)`, the `n`-th term of the
residue series `Φ(c) = Σ_{n≥1} 2/((cn)² − 1)`. This file exchanges the shell sum with the limit,
collapsing the shell-resolved statement into one limit:

* **`tendsto_shellSum_stripResidue`** : `Σ_{n≥1} shellDiffTerm c n i → Φ(c) = stripResidue c` as
  `i → ∞`, where `shellDiffTerm c n i` is the discrete `n`-th shell difference on the harmonic
  carrier. This is `(A−B)/i → Φ(c)` after Tonelli identifies `A/i = Σ_n aheadShell`, `B/i = Σ_n
  behindShell`.

The exchange is dominated convergence over `n` (`tendsto_tsum_of_dominated_convergence`). The
summable, `i`-uniform dominating bound `shellBound c n` is the technical core: writing the shell
difference as `region1 + tail`,
* **`region1_le`** bounds the bulk `k < (i+1)/2` by `36864/(cn)²` — a second-order Euler–Maclaurin
  estimate. The cancellation `A_k − B_k ≤ A_k·(cn)·(S^b_k − S^a_k)` with `S^b_k − S^a_k ≤ 4k(k+1)/(3i²)`
  turns the difference into a geometric second-moment sum `Σ k(k+1)ρ^k = 2ρ/(1−ρ)³` (`tsum_kk_geom`),
  controlled uniformly in `i` by `β³e^{−β}/(1−e^{−β})³ ≤ 216` (`phi_beta_bound`).
* **`tail_le`** bounds the ahead tail `k ≥ (i+1)/2` by `(3/2)(9/10)^{cn}/(cn−1)` — geometric in `n`.
  The offset-preserving profile `A_k ≤ e^{−cn/2i}((i+1)/(i+k+1))^{cn}` and the antitone `p`-series
  tail (`p_series_tail_le`) give a base `e^{−1/2i}·2(i+1)/(3i) ≤ 9/10` (`base_tail_le`).
Both bounds are summable in `n` (`shellBound_summable`), so the interchange holds.
-/
import GaloisForLFunctions.RHTower.LegStripContinuum
open MeasureTheory Real Set Filter Topology
noncomputable section
namespace RHTower

theorem tsum_kk_geom {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑' k : ℕ, (k:ℝ)*((k:ℝ)+1) * ρ^k = 2*ρ/(1-ρ)^3 := by
  have hnorm : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have h2 := tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hnorm
  have h1' := tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hnorm
  have e2 : ∀ k : ℕ, ((k+2).choose 2 : ℝ) = ((k:ℝ)+1)*((k:ℝ)+2)/2 := by
    intro k; rw [Nat.cast_choose_two]; push_cast; ring
  have e1 : ∀ k : ℕ, ((k+1).choose 1 : ℝ) = (k:ℝ)+1 := by
    intro k; rw [Nat.choose_one_right]; push_cast; ring
  have sc2 := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 2 hnorm
  have sc1 := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have hA : ∑' k : ℕ, (((k:ℝ)+1)*((k:ℝ)+2))*ρ^k = 2/(1-ρ)^3 := by
    have hc : ∀ k:ℕ, (((k:ℝ)+1)*((k:ℝ)+2))*ρ^k = 2*(((k+2).choose 2:ℝ)*ρ^k) := by
      intro k; rw [e2 k]; ring
    rw [tsum_congr hc, tsum_mul_left, h2, mul_one_div]
  have hB : ∑' k : ℕ, ((k:ℝ)+1)*ρ^k = 1/(1-ρ)^2 := by
    have hc : ∀ k:ℕ, ((k:ℝ)+1)*ρ^k = (((k+1).choose 1:ℝ))*ρ^k := by intro k; rw [e1 k]
    rw [tsum_congr hc, h1']
  have hsummA : Summable (fun k:ℕ => (((k:ℝ)+1)*((k:ℝ)+2))*ρ^k) := by
    apply (sc2.mul_left 2).congr; intro k; rw [e2 k]; ring
  have hsummB : Summable (fun k:ℕ => ((k:ℝ)+1)*ρ^k) := by
    apply sc1.congr; intro k; rw [e1 k]
  have hsplit : ∀ k:ℕ, (k:ℝ)*((k:ℝ)+1)*ρ^k
      = (((k:ℝ)+1)*((k:ℝ)+2))*ρ^k - 2*(((k:ℝ)+1)*ρ^k) := by intro k; ring
  rw [tsum_congr hsplit, Summable.tsum_sub hsummA (hsummB.mul_left 2), tsum_mul_left, hA, hB]
  have hne : (1-ρ) ≠ 0 := by nlinarith
  field_simp; ring

theorem phi_beta_bound {β : ℝ} (hβ : 0 < β) :
    β^3 * Real.exp (-β) / (1 - Real.exp (-β))^3 ≤ 216 := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have he : Real.exp (-β) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hep : 0 < Real.exp (-β) := Real.exp_pos _
  have hd : 0 < 1 - Real.exp (-β) := by linarith
  have hexpb : β + 1 ≤ Real.exp β := Real.add_one_le_exp β
  have h1p : (0:ℝ) < 1 + β := by linarith
  have hkey : β/(1+β) ≤ 1 - Real.exp (-β) := by
    have hrec : Real.exp (-β) ≤ 1/(1+β) := by
      rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le h1p (by linarith)
    have hid : (1:ℝ) - 1/(1+β) = β/(1+β) := by field_simp; ring
    linarith [hrec]
  have hcube : (β/(1+β))^3 ≤ (1 - Real.exp (-β))^3 := pow_le_pow_left₀ (by positivity) hkey 3
  have hnum : 0 ≤ β^3 * Real.exp (-β) := by positivity
  have hstep : β^3 * Real.exp (-β) / (1 - Real.exp (-β))^3
      ≤ β^3 * Real.exp (-β) / (β/(1+β))^3 := div_le_div_of_nonneg_left hnum (by positivity) hcube
  have hsimp : β^3 * Real.exp (-β) / (β/(1+β))^3 = Real.exp (-β) * (1+β)^3 := by
    rw [div_pow]; field_simp
  rw [hsimp] at hstep
  have hcube_exp : (Real.exp (β/3))^3 = Real.exp β := by
    rw [pow_three, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hcube2 : (1+β)^3 ≤ 216 * Real.exp β := by
    have h3 : 1 + β/3 ≤ Real.exp (β/3) := by have := Real.add_one_le_exp (β/3); linarith
    have h6 : (1:ℝ) + β ≤ 6 * Real.exp (β/3) := by nlinarith [h3, Real.exp_pos (β/3)]
    calc (1+β)^3 ≤ (6 * Real.exp (β/3))^3 := pow_le_pow_left₀ (by linarith) h6 3
      _ = 216 * (Real.exp (β/3))^3 := by ring
      _ = 216 * Real.exp β := by rw [hcube_exp]
  have hle : Real.exp (-β) * (1+β)^3 ≤ 216 := by
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos β)]
    calc (1+β)^3 ≤ 216 * Real.exp β := hcube2
      _ = Real.exp β * 216 := by ring
  linarith [hstep, hle]

def aheadTerm (c : ℝ) (n : ℕ+) (i k : ℕ) : ℝ :=
  Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
def behindTerm (c : ℝ) (n : ℕ+) (i k : ℕ) : ℝ :=
  Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)))

theorem gauss_sum_real (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j:ℝ)+1) = (m:ℝ)*((m:ℝ)+1)/2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring


theorem region1_le {c : ℝ} (hc : 1 < c) (n : ℕ+) {i : ℕ} (hi : 2 ≤ i) :
    (1/(i:ℝ)) * ∑ k ∈ Finset.range ((i+1)/2), (aheadTerm c n i k - behindTerm c n i k)
      ≤ 36864 / ((n:ℝ)*c)^2 := by
  obtain ⟨r, hr_def⟩ : ∃ r:ℝ, r = (n:ℝ)*c := ⟨_, rfl⟩
  rw [← hr_def]
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have hr1 : 1 < r := by rw [hr_def]; nlinarith
  have hr0 : 0 < r := by linarith
  have hipos : 0 < i := by omega
  have hi0 : (0:ℝ) < i := by exact_mod_cast hipos
  have hi1 : (1:ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
  obtain ⟨β, hβ_def⟩ : ∃ β:ℝ, β = r/(2*((i:ℝ)+1)) := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ_def]; positivity
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ:ℝ, ρ = Real.exp (-β) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ_def]; exact Real.exp_pos _
  have hρ1 : ρ < 1 := by rw [hρ_def, Real.exp_lt_one_iff]; linarith
  have h1mρ : 0 < 1 - ρ := by linarith
  have hden : 0 < (1-ρ)^3 := by positivity
  have hi3 : 0 < (i:ℝ)^3 := by positivity
  have hβ3 : β^3 = r^3/(8*((i:ℝ)+1)^3) := by rw [hβ_def]; field_simp; ring
  -- termwise bound
  have hterm : ∀ k ∈ Finset.range ((i+1)/2),
      aheadTerm c n i k - behindTerm c n i k
        ≤ ρ^k * (r * (4*(k:ℝ)*((k:ℝ)+1)/(3*(i:ℝ)^2))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h2k1 : 2*k+1 ≤ i := by omega
    have h2kr : 2*(k:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast h2k1
    have hki : (k:ℝ) ≤ (i:ℝ) := by
      have hh : k ≤ i := by omega
      exact_mod_cast hh
    obtain ⟨Sa, hSa⟩ : ∃ S:ℝ, S = ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := ⟨_, rfl⟩
    obtain ⟨Sb, hSb⟩ : ∃ S:ℝ, S = ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j) := ⟨_, rfl⟩
    have hSaSb : Sa ≤ Sb := by
      rw [hSa, hSb]; apply Finset.sum_le_sum
      intro j hj; rw [Finset.mem_range] at hj
      have hja : (0:ℝ) < (i:ℝ)-1-j := by
        have hh : j + 2 ≤ i := by omega
        have hh2 : (j:ℝ)+2 ≤ (i:ℝ) := by exact_mod_cast hh
        linarith
      apply one_div_le_one_div_of_le hja; linarith
    have hDnn : 0 ≤ Sb - Sa := by linarith
    have hbe : behindTerm c n i k = aheadTerm c n i k * Real.exp (-(r*(Sb-Sa))) := by
      rw [behindTerm, aheadTerm, ← Real.exp_add]; congr 1; rw [hr_def, hSa, hSb]; ring
    have hax : 0 ≤ aheadTerm c n i k := (Real.exp_pos _).le
    have h1e : aheadTerm c n i k - behindTerm c n i k ≤ aheadTerm c n i k * (r*(Sb-Sa)) := by
      rw [hbe]
      have hexp : (1:ℝ) - Real.exp (-(r*(Sb-Sa))) ≤ r*(Sb-Sa) := by
        linarith [Real.add_one_le_exp (-(r*(Sb-Sa)))]
      calc aheadTerm c n i k - aheadTerm c n i k * Real.exp (-(r*(Sb-Sa)))
          = aheadTerm c n i k * (1 - Real.exp (-(r*(Sb-Sa)))) := by ring
        _ ≤ aheadTerm c n i k * (r*(Sb-Sa)) := mul_le_mul_of_nonneg_left hexp hax
    have hSa_lb : (k:ℝ)/(2*((i:ℝ)+1)) ≤ Sa := by
      have hterm_lb : ∀ j ∈ Finset.range k, 1/((i:ℝ)+k) ≤ 1/((i:ℝ)+j+1) := by
        intro j hj; rw [Finset.mem_range] at hj
        have hjk : (j:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hj
        apply one_div_le_one_div_of_le (by positivity); linarith
      have hconst : (∑ j ∈ Finset.range k, (1/((i:ℝ)+k))) ≤ Sa := by
        rw [hSa]; exact Finset.sum_le_sum hterm_lb
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div] at hconst
      have hk_ik : (k:ℝ)/(2*((i:ℝ)+1)) ≤ (k:ℝ)/((i:ℝ)+k) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith
      linarith
    have hρk : ρ^k = Real.exp (-(r * ((k:ℝ)/(2*((i:ℝ)+1))))) := by
      rw [hρ_def, ← Real.exp_nat_mul]; congr 1; rw [hβ_def]; ring
    have hC : aheadTerm c n i k ≤ ρ^k := by
      rw [aheadTerm, hρk]; apply Real.exp_le_exp.mpr
      rw [← hSa]
      have heq : (n:ℝ)*(c/(2*(i:ℝ)) + c*Sa) = (n:ℝ)*(c/(2*(i:ℝ))) + r*Sa := by rw [hr_def]; ring
      have hoff : 0 ≤ (n:ℝ)*(c/(2*(i:ℝ))) := by positivity
      have h1 : r * ((k:ℝ)/(2*((i:ℝ)+1))) ≤ r*Sa := mul_le_mul_of_nonneg_left hSa_lb hr0.le
      rw [neg_mul, heq]; linarith
    have hD : Sb - Sa ≤ 4*(k:ℝ)*((k:ℝ)+1)/(3*(i:ℝ)^2) := by
      have hcombine : Sb - Sa = ∑ j ∈ Finset.range k, (1/((i:ℝ)-1-j) - 1/((i:ℝ)+j+1)) := by
        rw [hSa, hSb, ← Finset.sum_sub_distrib]
      have hterm_ub : ∀ j ∈ Finset.range k,
          1/((i:ℝ)-1-j) - 1/((i:ℝ)+j+1) ≤ 8*((j:ℝ)+1)/(3*(i:ℝ)^2) := by
        intro j hj; rw [Finset.mem_range] at hj
        have hja : (0:ℝ) < (i:ℝ)-1-j := by
          have hh : j + 2 ≤ i := by omega
          have hh2 : (j:ℝ)+2 ≤ (i:ℝ) := by exact_mod_cast hh
          linarith
        have hjb : (0:ℝ) < (i:ℝ)+j+1 := by positivity
        have h2j : 2*((j:ℝ)+1) ≤ (i:ℝ) := by
          have hh : 2*(j+1) ≤ i := by omega
          exact_mod_cast hh
        have habpos : 3*(i:ℝ)^2/4 ≤ ((i:ℝ)-1-j)*((i:ℝ)+j+1) := by
          have hsq : (2*((j:ℝ)+1))^2 ≤ (i:ℝ)^2 := pow_le_pow_left₀ (by positivity) h2j 2
          nlinarith [hsq]
        have heq : 1/((i:ℝ)-1-j) - 1/((i:ℝ)+j+1)
            = 2*((j:ℝ)+1)/(((i:ℝ)-1-j)*((i:ℝ)+j+1)) := by
          field_simp; ring
        rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
        have hmul := mul_le_mul_of_nonneg_left habpos (show (0:ℝ) ≤ 8*((j:ℝ)+1) by positivity)
        have hLid : 2*((j:ℝ)+1) * (3*(i:ℝ)^2) = 8*((j:ℝ)+1) * (3*(i:ℝ)^2/4) := by ring
        rw [hLid]; exact hmul
      calc Sb - Sa = ∑ j ∈ Finset.range k, (1/((i:ℝ)-1-j) - 1/((i:ℝ)+j+1)) := hcombine
        _ ≤ ∑ j ∈ Finset.range k, 8*((j:ℝ)+1)/(3*(i:ℝ)^2) := Finset.sum_le_sum hterm_ub
        _ = (8/(3*(i:ℝ)^2)) * ∑ j ∈ Finset.range k, ((j:ℝ)+1) := by rw [Finset.mul_sum]; congr 1; ext j; ring
        _ = (8/(3*(i:ℝ)^2)) * ((k:ℝ)*((k:ℝ)+1)/2) := by rw [gauss_sum_real]
        _ = 4*(k:ℝ)*((k:ℝ)+1)/(3*(i:ℝ)^2) := by ring
    calc aheadTerm c n i k - behindTerm c n i k
        ≤ aheadTerm c n i k * (r*(Sb-Sa)) := h1e
      _ ≤ ρ^k * (r*(Sb-Sa)) := mul_le_mul_of_nonneg_right hC (mul_nonneg hr0.le hDnn)
      _ ≤ ρ^k * (r * (4*(k:ℝ)*((k:ℝ)+1)/(3*(i:ℝ)^2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hr0.le) (pow_nonneg hρ0.le k)
  -- sum the termwise bound and finish
  have hsumm_kk : Summable (fun k:ℕ => ((k:ℝ)*((k:ℝ)+1))*ρ^k) := by
    have hnorm : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0.le]; exact hρ1
    apply ((summable_pow_mul_geometric_of_norm_lt_one 2 hnorm).add
      (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm)).congr
    intro k; ring
  have hsumtsum : ∑ k ∈ Finset.range ((i+1)/2), ((k:ℝ)*((k:ℝ)+1))*ρ^k ≤ 2*ρ/(1-ρ)^3 := by
    rw [← tsum_kk_geom hρ0.le hρ1]
    exact hsumm_kk.sum_le_tsum _ (fun k _ => by positivity)
  have hphi := phi_beta_bound hβ0
  rw [← hρ_def] at hphi
  have hstep1 : ∑ k ∈ Finset.range ((i+1)/2), (aheadTerm c n i k - behindTerm c n i k)
      ≤ (4*r/(3*(i:ℝ)^2)) * (2*ρ/(1-ρ)^3) := by
    calc ∑ k ∈ Finset.range ((i+1)/2), (aheadTerm c n i k - behindTerm c n i k)
        ≤ ∑ k ∈ Finset.range ((i+1)/2), ρ^k * (r * (4*(k:ℝ)*((k:ℝ)+1)/(3*(i:ℝ)^2))) :=
          Finset.sum_le_sum hterm
      _ = (4*r/(3*(i:ℝ)^2)) * ∑ k ∈ Finset.range ((i+1)/2), ((k:ℝ)*((k:ℝ)+1))*ρ^k := by
          rw [Finset.mul_sum]; congr 1; ext k; ring
      _ ≤ (4*r/(3*(i:ℝ)^2)) * (2*ρ/(1-ρ)^3) := mul_le_mul_of_nonneg_left hsumtsum (by positivity)
  -- final arithmetic
  have hphi_cl : r^3*ρ ≤ 1728*((i:ℝ)+1)^3*(1-ρ)^3 := by
    have h := hphi
    rw [div_le_iff₀ hden] at h
    rw [hβ3, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h
    nlinarith [h]
  have hi18 : ((i:ℝ)+1)^3 ≤ 8*(i:ℝ)^3 := by nlinarith [hi1]
  have hLHS : (1/(i:ℝ)) * ((4*r/(3*(i:ℝ)^2)) * (2*ρ/(1-ρ)^3)) = (8*r*ρ)/(3*(i:ℝ)^3*(1-ρ)^3) := by
    field_simp; ring
  calc (1/(i:ℝ)) * ∑ k ∈ Finset.range ((i+1)/2), (aheadTerm c n i k - behindTerm c n i k)
      ≤ (1/(i:ℝ)) * ((4*r/(3*(i:ℝ)^2)) * (2*ρ/(1-ρ)^3)) :=
        mul_le_mul_of_nonneg_left hstep1 (by positivity)
    _ = (8*r*ρ)/(3*(i:ℝ)^3*(1-ρ)^3) := hLHS
    _ ≤ 36864/r^2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hphi_cl, hi18, mul_le_mul_of_nonneg_right hi18 (pow_nonneg (le_of_lt h1mρ) 3),
          pow_nonneg (le_of_lt h1mρ) 3, hr0, hρ0]

theorem p_series_tail_le {r : ℝ} (hr : 1 < r) {M : ℕ} (hM : 2 ≤ M) :
    ∑' k : ℕ, ((M:ℝ)+(k:ℝ))^(-r) ≤ ((M:ℝ)-1)^(1-r)/(r-1) := by
  have hr0 : 0 < r := by linarith
  have hMc : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hM1pos : (0:ℝ) < (M:ℝ)-1 := by linarith
  have hMcast : ((M-1 : ℕ):ℝ) = (M:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; simp
  have hFint : IntegrableOn (fun x:ℝ => x^(-r)) (Ioi ((M:ℝ)-1)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hM1pos
  have hnnF : ∀ x, (M:ℝ)-1 ≤ x → (0:ℝ) ≤ x^(-r) := fun x hx => Real.rpow_nonneg (by linarith [hM1pos]) _
  have hintval : ∫ x in Ioi ((M:ℝ)-1), x^(-r) = ((M:ℝ)-1)^(1-r)/(r-1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : (-r) < -1) hM1pos,
      show (-r+1) = -(r-1) by ring, show (1-r) = -(r-1) by ring]
    rw [Real.rpow_neg hM1pos.le]
    field_simp
  apply tsum_le_of_sum_range_le (fun k => by positivity)
  intro m
  have hanti : AntitoneOn (fun x:ℝ => x^(-r)) (Icc ((M-1:ℕ):ℝ) ((M-1+m:ℕ):ℝ)) := by
    intro a ha b hb hab
    rw [Set.mem_Icc, hMcast] at ha
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
  have hsli := AntitoneOn.sum_le_integral_Ico (f := fun x:ℝ => x^(-r))
    (show M-1 ≤ M-1+m by omega) hanti
  have hLHSeq : ∑ i ∈ Finset.Ico (M-1) (M-1+m), ((↑(i+1):ℝ))^(-r)
      = ∑ k ∈ Finset.range m, ((M:ℝ)+(k:ℝ))^(-r) := by
    rw [Finset.sum_Ico_eq_sum_range, show M-1+m-(M-1) = m from by omega]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [show M-1+k+1 = M+k from by omega]; push_cast; ring
  have hRHSle : ∫ x in ((M-1:ℕ):ℝ)..((M-1+m:ℕ):ℝ), x^(-r) ≤ ((M:ℝ)-1)^(1-r)/(r-1) := by
    rw [← hintval]
    have hab : ((M-1:ℕ):ℝ) ≤ ((M-1+m:ℕ):ℝ) := by exact_mod_cast (show M-1 ≤ M-1+m by omega)
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_mono_set hFint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hnnF x (le_of_lt hx)
    · refine Filter.Eventually.of_forall (fun x hx => ?_)
      exact hMcast ▸ hx.1
  rw [hLHSeq] at hsli
  linarith [hsli, hRHSle]

theorem base_tail_le {i : ℕ} (hi : 2 ≤ i) :
    Real.exp (-(1/(2*(i:ℝ)))) * (2*((i:ℝ)+1)/(3*(i:ℝ))) ≤ 9/10 := by
  have hi0 : (0:ℝ) < i := by positivity
  have hi1 : (1:ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
  have hrec : Real.exp (-(1/(2*(i:ℝ)))) ≤ 1/(1+1/(2*(i:ℝ))) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have := Real.add_one_le_exp (1/(2*(i:ℝ))); linarith
  have hpos : (0:ℝ) ≤ 2*((i:ℝ)+1)/(3*(i:ℝ)) := by positivity
  calc Real.exp (-(1/(2*(i:ℝ)))) * (2*((i:ℝ)+1)/(3*(i:ℝ)))
      ≤ (1/(1+1/(2*(i:ℝ)))) * (2*((i:ℝ)+1)/(3*(i:ℝ))) := mul_le_mul_of_nonneg_right hrec hpos
    _ ≤ 9/10 := by
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        have hexp : (1+1/(2*(i:ℝ)))*(3*(i:ℝ)) = 3*(i:ℝ)+3/2 := by field_simp
        rw [hexp]; nlinarith [hi1]

theorem tail_le {c : ℝ} (hc : 1 < c) (n : ℕ+) {i : ℕ} (hi : 2 ≤ i) :
    (1/(i:ℝ)) * ∑' m:ℕ, aheadTerm c n i (m + (i+1)/2)
      ≤ (3/2) * (9/10)^((n:ℝ)*c) / ((n:ℝ)*c - 1) := by
  obtain ⟨r, hr_def⟩ : ∃ r:ℝ, r = (n:ℝ)*c := ⟨_, rfl⟩
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have hr1 : 1 < r := by rw [hr_def]; nlinarith
  have hr0 : 0 < r := by linarith
  have hipos : 0 < i := by omega
  have hi0 : (0:ℝ) < i := by exact_mod_cast hipos
  have hi1 : (1:ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
  set K := (i+1)/2 with hK_def
  have hK1 : 1 ≤ K := by rw [hK_def]; omega
  have hKi : (i:ℝ) ≤ 2*(K:ℝ) := by
    have : i ≤ 2*K := by rw [hK_def]; omega
    exact_mod_cast this
  set M := i+1+K with hM_def
  have hM2 : 2 ≤ M := by rw [hM_def]; omega
  have hMR : (M:ℝ) = (i:ℝ)+1+(K:ℝ) := by rw [hM_def]; push_cast; ring
  have hM1R : ((M:ℝ)-1) = (i:ℝ)+(K:ℝ) := by rw [hMR]; ring
  -- profile bound
  have hprof : ∀ m:ℕ, aheadTerm c n i (m+K)
      ≤ Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * ((M:ℝ)+(m:ℝ))^(-r)) := by
    intro m
    rw [aheadTerm]
    have hSa_lb : Real.log (((M:ℝ)+(m:ℝ))/((i:ℝ)+1))
        ≤ ∑ j ∈ Finset.range (m+K), 1/((i:ℝ)+j+1) := by
      have h := harmonic_log_upper (i+1) (by omega) (m+K)
      have hcast1 : ((i+1:ℕ):ℝ) + ((m+K:ℕ):ℝ) = (M:ℝ)+(m:ℝ) := by rw [hMR]; push_cast; ring
      have hcast2 : ((i+1:ℕ):ℝ) = (i:ℝ)+1 := by push_cast; ring
      rw [hcast1, hcast2] at h
      refine le_trans h (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro j _; congr 1; ring
    have ht : (0:ℝ) < ((M:ℝ)+(m:ℝ))/((i:ℝ)+1) := by
      have : (0:ℝ) < (M:ℝ)+(m:ℝ) := by rw [hMR]; positivity
      positivity
    have hexpSa : Real.exp (-(r * ∑ j ∈ Finset.range (m+K), 1/((i:ℝ)+j+1)))
        ≤ ((i:ℝ)+1)^r * ((M:ℝ)+(m:ℝ))^(-r) := by
      have hle : -(r * ∑ j ∈ Finset.range (m+K), 1/((i:ℝ)+j+1))
          ≤ -(r * Real.log (((M:ℝ)+(m:ℝ))/((i:ℝ)+1))) := by
        have := mul_le_mul_of_nonneg_left hSa_lb hr0.le
        linarith
      refine le_trans (Real.exp_le_exp.mpr hle) (le_of_eq ?_)
      rw [Real.rpow_def_of_pos (show (0:ℝ)<(i:ℝ)+1 by positivity),
          Real.rpow_def_of_pos (show (0:ℝ)<(M:ℝ)+(m:ℝ) by rw [hMR]; positivity),
          ← Real.exp_add]
      congr 1
      rw [Real.log_div (by rw [hMR]; positivity) (by positivity)]
      ring
    calc Real.exp (-(n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range (m+K), 1/((i:ℝ)+j+1)))
        = Real.exp (-(r/(2*(i:ℝ)))) *
            Real.exp (-(r * ∑ j ∈ Finset.range (m+K), 1/((i:ℝ)+j+1))) := by
          rw [← Real.exp_add]; congr 1; rw [hr_def]; ring
      _ ≤ Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * ((M:ℝ)+(m:ℝ))^(-r)) :=
          mul_le_mul_of_nonneg_left hexpSa (Real.exp_pos _).le
  -- summability of the p-series and aheadTerm tail
  have hg_summ : Summable (fun m:ℕ => ((M:ℝ)+(m:ℝ))^(-r)) := by
    have hbase : Summable (fun k:ℕ => ((k:ℝ))^(-r)) := Real.summable_nat_rpow.mpr (by linarith)
    have := (summable_nat_add_iff M).mpr hbase
    apply this.congr; intro m; rw [add_comm]; push_cast; ring
  have hah_summ : Summable (fun m:ℕ => aheadTerm c n i (m+K)) :=
    Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hprof
      ((hg_summ.mul_left (((i:ℝ)+1)^r)).mul_left (Real.exp (-(r/(2*(i:ℝ))))))
  have htsum_le : ∑' m:ℕ, aheadTerm c n i (m+K)
      ≤ Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * (((M:ℝ)-1)^(1-r)/(r-1))) := by
    have h1 := Summable.tsum_le_tsum hprof hah_summ
      ((hg_summ.mul_left (((i:ℝ)+1)^r)).mul_left (Real.exp (-(r/(2*(i:ℝ))))))
    rw [tsum_mul_left, tsum_mul_left] at h1
    have h2 : ∑' m:ℕ, ((M:ℝ)+(m:ℝ))^(-r) ≤ ((M:ℝ)-1)^(1-r)/(r-1) := p_series_tail_le hr1 hM2
    calc ∑' m:ℕ, aheadTerm c n i (m+K)
        ≤ Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * ∑' m:ℕ, ((M:ℝ)+(m:ℝ))^(-r)) := h1
      _ ≤ Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * (((M:ℝ)-1)^(1-r)/(r-1))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
  -- final base argument
  rw [← hr_def]
  have hbase_le : Real.exp (-(1/(2*(i:ℝ)))) * (2*((i:ℝ)+1)/(3*(i:ℝ))) ≤ 9/10 := base_tail_le hi
  have hbase0 : 0 ≤ Real.exp (-(1/(2*(i:ℝ)))) * (2*((i:ℝ)+1)/(3*(i:ℝ))) := by positivity
  have h3i : (0:ℝ) < 3*(i:ℝ)/2 := by positivity
  have hiK : 3*(i:ℝ)/2 ≤ (i:ℝ)+(K:ℝ) := by linarith [hKi]
  have hp1 : ((i:ℝ)+(K:ℝ))^(1-r) ≤ (3*(i:ℝ)/2)^(1-r) :=
    Real.rpow_le_rpow_of_nonpos h3i hiK (by linarith)
  have e1 : Real.exp (-(r/(2*(i:ℝ)))) = (Real.exp (-(1/(2*(i:ℝ)))))^r := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; ring
  have e2 : (3*(i:ℝ)/2)^(1-r) = (3*(i:ℝ)/2) * (3*(i:ℝ)/2)^(-r) := by
    rw [show (1-r) = 1+(-r) by ring, Real.rpow_add (by positivity), Real.rpow_one]
  have e3 : ((i:ℝ)+1)^r * (3*(i:ℝ)/2)^(-r) = (2*((i:ℝ)+1)/(3*(i:ℝ)))^r := by
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv,
      ← Real.div_rpow (by positivity) (by positivity)]
    congr 1; field_simp
  have heq : Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * (3*(i:ℝ)/2)^(1-r))
      = (3*(i:ℝ)/2) * (Real.exp (-(1/(2*(i:ℝ)))) * (2*((i:ℝ)+1)/(3*(i:ℝ))))^r := by
    rw [e1, Real.mul_rpow (Real.exp_pos _).le (by positivity), e2,
      show ((i:ℝ)+1)^r * ((3*(i:ℝ)/2) * (3*(i:ℝ)/2)^(-r))
        = (3*(i:ℝ)/2) * (((i:ℝ)+1)^r * (3*(i:ℝ)/2)^(-r)) by ring, e3]
    ring
  have hkey : Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * ((i:ℝ)+(K:ℝ))^(1-r))
      ≤ (3*(i:ℝ)/2) * (9/10)^r := by
    calc Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * ((i:ℝ)+(K:ℝ))^(1-r))
        ≤ Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * (3*(i:ℝ)/2)^(1-r)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ = (3*(i:ℝ)/2) * (Real.exp (-(1/(2*(i:ℝ)))) * (2*((i:ℝ)+1)/(3*(i:ℝ))))^r := heq
      _ ≤ (3*(i:ℝ)/2) * (9/10)^r := by
          apply mul_le_mul_of_nonneg_left _ h3i.le
          exact Real.rpow_le_rpow hbase0 hbase_le hr0.le
  calc (1/(i:ℝ)) * ∑' m:ℕ, aheadTerm c n i (m + (i+1)/2)
      ≤ (1/(i:ℝ)) * (Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * (((M:ℝ)-1)^(1-r)/(r-1)))) :=
        mul_le_mul_of_nonneg_left (by rw [← hK_def]; exact htsum_le) (by positivity)
    _ = (1/(i:ℝ)) * (1/(r-1)) *
          (Real.exp (-(r/(2*(i:ℝ)))) * (((i:ℝ)+1)^r * ((i:ℝ)+(K:ℝ))^(1-r))) := by
        rw [hM1R]; ring
    _ ≤ (1/(i:ℝ)) * (1/(r-1)) * ((3*(i:ℝ)/2) * (9/10)^r) := by
        apply mul_le_mul_of_nonneg_left hkey
        apply mul_nonneg (by positivity)
        rw [one_div]; exact inv_nonneg.mpr (by linarith)
    _ = 3/2 * (9/10)^r / (r-1) := by field_simp

/-- The `n`-th shell difference on the harmonic carrier: the discrete ahead shell (over all poles
ahead of the gap midpoint) minus the behind shell (over the finitely many poles behind), each scaled
by `1/i`. Its `i → ∞` limit is `2/((cn)² − 1)` (`tendsto_shellDiff`). -/
def shellDiffTerm (c : ℝ) (n : ℕ+) (i : ℕ) : ℝ :=
  (1/(i:ℝ)) * ∑' k : ℕ, aheadTerm c n i k
    - (1/(i:ℝ)) * ∑ k ∈ Finset.range i, behindTerm c n i k

/-- The summable, `i`-uniform dominating bound: bulk term `36864/(cn)²` plus geometric tail. -/
def shellBound (c : ℝ) (n : ℕ+) : ℝ :=
  36864/((n:ℝ)*c)^2 + (3/2)*(9/10)^((n:ℝ)*c)/((n:ℝ)*c-1)

set_option maxHeartbeats 800000 in
/-- The ahead shell is summable: `aheadTerm c n i k ≤ (i+1)^{cn}(i+1+k)^{−cn}`, a convergent
`p`-series (`cn > 1`). -/
theorem aheadTerm_summable {c : ℝ} (hc : 1 < c) (n : ℕ+) {i : ℕ} (hi : 2 ≤ i) :
    Summable (fun k:ℕ => aheadTerm c n i k) := by
  obtain ⟨r, hr_def⟩ : ∃ r:ℝ, r = (n:ℝ)*c := ⟨_, rfl⟩
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have hr1 : 1 < r := by rw [hr_def]; nlinarith
  have hr0 : 0 < r := by linarith
  have hi1 : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast (show 1 ≤ i by omega)
  have hprof : ∀ k:ℕ, aheadTerm c n i k ≤ ((i:ℝ)+1)^r * ((i:ℝ)+1+(k:ℝ))^(-r) := by
    intro k
    rw [aheadTerm]
    have hSa : Real.log (((i:ℝ)+1+(k:ℝ))/((i:ℝ)+1)) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := by
      have h := harmonic_log_upper (i+1) (by omega) k
      have hcast2 : ((i+1:ℕ):ℝ) = (i:ℝ)+1 := by push_cast; ring
      rw [hcast2] at h
      refine le_trans h (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro j _; congr 1; ring
    have hval : Real.exp (-(r * Real.log (((i:ℝ)+1+(k:ℝ))/((i:ℝ)+1))))
        = ((i:ℝ)+1)^r * ((i:ℝ)+1+(k:ℝ))^(-r) := by
      rw [Real.rpow_def_of_pos (show (0:ℝ)<(i:ℝ)+1 by positivity),
          Real.rpow_def_of_pos (show (0:ℝ)<(i:ℝ)+1+(k:ℝ) by positivity), ← Real.exp_add]
      congr 1
      rw [Real.log_div (by positivity) (by positivity)]; ring
    have hexpSa : Real.exp (-(r * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
        ≤ ((i:ℝ)+1)^r * ((i:ℝ)+1+(k:ℝ))^(-r) := by
      rw [← hval]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hSa hr0.le; linarith
    refine le_trans ?_ hexpSa
    apply Real.exp_le_exp.mpr
    have heq : (n:ℝ) * (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))
        = (n:ℝ)*(c/(2*(i:ℝ))) + r * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := by rw [hr_def]; ring
    rw [neg_mul, heq]
    have hoff : 0 ≤ (n:ℝ)*(c/(2*(i:ℝ))) := by positivity
    linarith
  have hsumm : Summable (fun k:ℕ => ((i:ℝ)+1)^r * ((i:ℝ)+1+(k:ℝ))^(-r)) := by
    have hb : Summable (fun k:ℕ => ((k:ℝ))^(-r)) := Real.summable_nat_rpow.mpr (by linarith)
    have hs : Summable (fun k:ℕ => ((k+(i+1):ℕ):ℝ)^(-r)) := (summable_nat_add_iff (i+1)).mpr hb
    refine (hs.mul_left (((i:ℝ)+1)^r)).congr (fun k => ?_)
    congr 2
    push_cast; ring
  exact Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) hprof hsumm

/-- Behind poles sit farther from the midpoint than the corresponding ahead poles, so termwise
`behindTerm ≤ aheadTerm` (for `k < i`). -/
theorem behindTerm_le_aheadTerm {c : ℝ} (hc : 1 < c) (n : ℕ+) {i : ℕ}
    {k : ℕ} (hk : k < i) : behindTerm c n i k ≤ aheadTerm c n i k := by
  rw [behindTerm, aheadTerm]
  apply Real.exp_le_exp.mpr
  have hSaSb : ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j) := by
    apply Finset.sum_le_sum
    intro j hj; rw [Finset.mem_range] at hj
    have hja : (0:ℝ) < (i:ℝ)-1-j := by
      have hh : j + 2 ≤ i := by omega
      have hc2 : (j:ℝ)+2 ≤ (i:ℝ) := by exact_mod_cast hh
      linarith
    apply one_div_le_one_div_of_le hja; linarith
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.pos
  have hc0 : 0 < c := by linarith
  have h := mul_le_mul_of_nonneg_left hSaSb (show (0:ℝ) ≤ (n:ℝ)*c by positivity)
  nlinarith [h]

/-- The shell difference is nonnegative: the full ahead shell dominates the finite behind shell. -/
theorem shellDiffTerm_nonneg {c : ℝ} (hc : 1 < c) (n : ℕ+) {i : ℕ} (hi : 2 ≤ i) :
    0 ≤ shellDiffTerm c n i := by
  rw [shellDiffTerm, sub_nonneg]
  have hi0 : (0:ℝ) < i := by positivity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 : ∑ k ∈ Finset.range i, behindTerm c n i k ≤ ∑ k ∈ Finset.range i, aheadTerm c n i k := by
    apply Finset.sum_le_sum; intro k hk; rw [Finset.mem_range] at hk
    exact behindTerm_le_aheadTerm hc n hk
  have h2 : ∑ k ∈ Finset.range i, aheadTerm c n i k ≤ ∑' k:ℕ, aheadTerm c n i k :=
    (aheadTerm_summable hc n hi).sum_le_tsum _ (fun k _ => (Real.exp_pos _).le)
  linarith

/-- The `i`-uniform dominating bound: `shellDiffTerm ≤ region1 + tail ≤ shellBound`. The behind
shell is split at `(i+1)/2`; the leftover behind terms are dropped (nonnegative), the ahead sum is
split into head (`region1_le`) and tail (`tail_le`). -/
theorem shellDiffTerm_le {c : ℝ} (hc : 1 < c) (n : ℕ+) {i : ℕ} (hi : 2 ≤ i) :
    shellDiffTerm c n i ≤ shellBound c n := by
  rw [shellDiffTerm, shellBound]
  have hi0 : (0:ℝ) < i := by positivity
  have hKi : (i+1)/2 ≤ i := by omega
  have hsplit := Summable.sum_add_tsum_nat_add ((i+1)/2) (aheadTerm_summable hc n hi)
  rw [← hsplit]
  have hsub : Finset.range ((i+1)/2) ⊆ Finset.range i := by
    intro x hx; simp only [Finset.mem_range] at *; omega
  have hbehind : ∑ k ∈ Finset.range ((i+1)/2), behindTerm c n i k
      ≤ ∑ k ∈ Finset.range i, behindTerm c n i k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => (Real.exp_pos _).le)
  calc (1/(i:ℝ)) * (∑ k ∈ Finset.range ((i+1)/2), aheadTerm c n i k
          + ∑' m, aheadTerm c n i (m+(i+1)/2))
        - (1/(i:ℝ)) * ∑ k ∈ Finset.range i, behindTerm c n i k
      ≤ (1/(i:ℝ)) * (∑ k ∈ Finset.range ((i+1)/2), aheadTerm c n i k
          + ∑' m, aheadTerm c n i (m+(i+1)/2))
        - (1/(i:ℝ)) * ∑ k ∈ Finset.range ((i+1)/2), behindTerm c n i k :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left hbehind (by positivity)) _
    _ = (1/(i:ℝ)) * ∑ k ∈ Finset.range ((i+1)/2), (aheadTerm c n i k - behindTerm c n i k)
        + (1/(i:ℝ)) * ∑' m, aheadTerm c n i (m+(i+1)/2) := by
          rw [Finset.sum_sub_distrib]; ring
    _ ≤ 36864/((n:ℝ)*c)^2 + (3/2)*(9/10)^((n:ℝ)*c)/((n:ℝ)*c-1) :=
        add_le_add (region1_le hc n hi) (tail_le hc n hi)

/-- The dominating bound is summable: the bulk term is `O(1/n²)`, the tail term geometric. -/
theorem shellBound_summable {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ+ => shellBound c n) := by
  have hc0 : 0 < c := by linarith
  apply Summable.add
  · have hbase : Summable (fun n : ℕ+ => (36864/c^2) * (1/(n:ℝ)^2)) :=
      (((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).comp_injective
        PNat.coe_injective).mul_left _
    apply hbase.congr; intro n
    have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.pos
    field_simp
  · have hcc1 : (0:ℝ) < c-1 := by linarith
    have hnc : ∀ m:ℕ+, (1:ℝ) < (m:ℝ)*c := by
      intro m
      have hm : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast m.pos
      nlinarith
    have hq : ((9:ℝ)/10)^c < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
    have hq0 : (0:ℝ) ≤ ((9:ℝ)/10)^c := by positivity
    have hgeo : Summable (fun m : ℕ+ => (3/2) * (((9:ℝ)/10)^c)^(m:ℕ) / (c-1)) :=
      (((summable_geometric_of_lt_one hq0 hq).comp_injective PNat.coe_injective).mul_left
        (3/2)).div_const _
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hgeo
    · exact div_nonneg (by positivity) (by have := hnc m; linarith)
    · have hnc1 : (0:ℝ) < (m:ℝ)*c-1 := by have := hnc m; linarith
      have hn1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast m.pos
      have hpow : ((9:ℝ)/10)^((m:ℝ)*c) = (((9:ℝ)/10)^c)^(m:ℕ) := by
        rw [← Real.rpow_natCast (((9:ℝ)/10)^c) (m:ℕ), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 9/10)]
        congr 1; ring
      rw [hpow]
      exact div_le_div_of_nonneg_left (by positivity) hcc1 (by nlinarith [hn1])

/-- **The shell-sum interchange: `Σ_{n≥1} shellDiffTerm c n i → Φ(c)` as `i → ∞`.** Dominated
convergence over `n` exchanges the shell sum with the `i`-limit: each shell converges
(`tendsto_shellDiff`) to the residue-series term `2/((cn)² − 1)`, whose sum over `n` is `Φ(c) =
stripResidue c` (`stripResidue_eq_tsum`); the shell differences are dominated uniformly in `i` by the
summable `shellBound`. This collapses the shell-resolved balance into the literal single limit
`(A−B)/i → Φ(c)`. -/
theorem tendsto_shellSum_stripResidue {c : ℝ} (hc : 1 < c) :
    Tendsto (fun i : ℕ => ∑' n : ℕ+, shellDiffTerm c n i) atTop (𝓝 (stripResidue c)) := by
  have hgeq : (∑' n : ℕ+, (2 / (((n:ℝ)*c)^2 - 1))) = stripResidue c := by
    rw [stripResidue_eq_tsum hc]; exact tsum_congr (fun n => by rw [mul_comm])
  rw [← hgeq]
  refine tendsto_tsum_of_dominated_convergence (shellBound_summable hc) (fun n => ?_) ?_
  · exact tendsto_shellDiff hc n
  · filter_upwards [eventually_ge_atTop 2] with i hi n
    rw [Real.norm_eq_abs, abs_of_nonneg (shellDiffTerm_nonneg hc n hi)]
    exact shellDiffTerm_le hc n hi

end RHTower
