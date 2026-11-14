import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.FiberwiseSlivers

/-!
# The fiberwise floor

A `FiberCert` lists contiguous four-branch subintervals of `[0, lo]`, two-branch subintervals of
`[hi, 1/2]` and the two slivers. Folding `(0, 1)` onto the two fiber regions
(`six_interval_folding_diag`, `six_interval_folding_primeTwo`) and adding the subinterval and
sliver bounds gives `FiberCert.bound`.
-/

open Real MeasureTheory Set Finset intervalIntegral
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

open SelectivePositivityAndThresholdLaws

/-- Contiguity of four-branch subintervals from `x` to `y`. -/
def chain4 : ℚ → List P4Sub → ℚ → Bool
  | x, [], y => decide (x = y)
  | x, D :: Ds, y => decide (D.sa = x) && decide (0 < D.ds) && chain4 (x + D.ds) Ds y

/-- Contiguity of two-branch subintervals from `x` to `y`. -/
def chain2 : ℚ → List P2Sub → ℚ → Bool
  | x, [], y => decide (x = y)
  | x, D :: Ds, y => decide (D.ua = x) && decide (0 < D.du) && chain2 (x + D.du) Ds y

theorem le_of_chain4 : ∀ {x y : ℚ} {Ds : List P4Sub}, chain4 x Ds y = true → x ≤ y
  | x, y, [], h => by simp only [chain4, decide_eq_true_eq] at h; exact h.le
  | x, y, D :: Ds, h => by
    simp only [chain4, Bool.and_eq_true, decide_eq_true_eq] at h
    have := le_of_chain4 h.2
    linarith [h.1.2]

theorem le_of_chain2 : ∀ {x y : ℚ} {Ds : List P2Sub}, chain2 x Ds y = true → x ≤ y
  | x, y, [], h => by simp only [chain2, decide_eq_true_eq] at h; exact h.le
  | x, y, D :: Ds, h => by
    simp only [chain2, Bool.and_eq_true, decide_eq_true_eq] at h
    have := le_of_chain2 h.2
    linarith [h.1.2]

/-- The summed certificate cost `mᵀ Qhat m + ∑ pertHat_k m_k²` of a list of subintervals. -/
noncomputable def cost4 (K : ℕ) (Ds : List P4Sub) (m : Fin K → ℝ) : ℝ :=
  (Ds.map fun D => quadR K D.Qhat m + ∑ k : Fin K, (vecQ D.pertHat k : ℝ) * m k ^ 2).sum

noncomputable def cost2 (K : ℕ) (Ds : List P2Sub) (m : Fin K → ℝ) : ℝ :=
  (Ds.map fun D => quadR K D.Qhat m + ∑ k : Fin K, (vecQ D.pertHat k : ℝ) * m k ^ 2).sum

theorem integral_chain4 {S : SectorData} (hS : S.valid = true) {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1))
    (m : Fin S.K → ℝ) :
    ∀ (Ds : List P4Sub) (x y : ℚ), chain4 x Ds y = true → (∀ D ∈ Ds, D.check S = true) →
      0 ≤ x → (y : ℝ) ≤ (1 - primeThreeOffset) / 2 →
      -(cost4 S.K Ds m) ≤ ∫ s in (x : ℝ)..(y : ℝ), f4Integrand S G m s
  | [], x, y, h, _, _, _ => by
    simp only [chain4, decide_eq_true_eq] at h
    subst h; simp [cost4]
  | D :: Ds, x, y, h, hc, hx, hy => by
    simp only [chain4, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hsa, hds⟩, hrest⟩ := h
    have hmid : x + D.ds ≤ y := le_of_chain4 hrest
    have hx' : (0 : ℝ) ≤ x := Rat.cast_nonneg.mpr hx
    have hmid' : ((x + D.ds : ℚ) : ℝ) ≤ y := Rat.cast_le.mpr hmid
    have hds' : (0 : ℝ) < D.ds := Rat.cast_pos.mpr hds
    have hD := P4Sub.bound hS (hc D (List.mem_cons_self ..)) hGc hiPot m
    rw [hsa] at hD
    have ih := integral_chain4 hS hGc hiPot m Ds (x + D.ds) y hrest
      (fun D' hD' => hc D' (List.mem_cons_of_mem _ hD')) (by linarith) hy
    have i1 := intervalIntegrable_f4Integrand (S := S) hGc hiPot m hx' (α := (x : ℝ))
      (β := (x : ℝ) + D.ds) (by linarith) (by push_cast at hmid'; linarith)
    have i2 := intervalIntegrable_f4Integrand (S := S) hGc hiPot m (α := (x : ℝ) + D.ds)
      (β := (y : ℝ)) (by linarith) (by push_cast at hmid'; linarith) hy
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    push_cast at ih
    simp only [cost4, List.map_cons, List.sum_cons] at ih ⊢
    linarith

theorem integral_chain2 {S : SectorData} (hS : S.valid = true) {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1))
    (m : Fin S.K → ℝ) :
    ∀ (Ds : List P2Sub) (x y : ℚ), chain2 x Ds y = true → (∀ D ∈ Ds, D.check S = true) →
      0 ≤ x → (y : ℝ) ≤ 1 →
      -(cost2 S.K Ds m) ≤ ∫ u in (x : ℝ)..(y : ℝ), f2Integrand S G m u
  | [], x, y, h, _, _, _ => by
    simp only [chain2, decide_eq_true_eq] at h
    subst h; simp [cost2]
  | D :: Ds, x, y, h, hc, hx, hy => by
    simp only [chain2, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hua, hdu⟩, hrest⟩ := h
    have hmid : x + D.du ≤ y := le_of_chain2 hrest
    have hx' : (0 : ℝ) ≤ x := Rat.cast_nonneg.mpr hx
    have hmid' : ((x + D.du : ℚ) : ℝ) ≤ y := Rat.cast_le.mpr hmid
    have hdu' : (0 : ℝ) < D.du := Rat.cast_pos.mpr hdu
    have hD := P2Sub.bound hS (hc D (List.mem_cons_self ..)) hGc hiPot m
    rw [hua] at hD
    have ih := integral_chain2 hS hGc hiPot m Ds (x + D.du) y hrest
      (fun D' hD' => hc D' (List.mem_cons_of_mem _ hD')) (by linarith) hy
    have i1 := intervalIntegrable_f2Integrand (S := S) hGc hiPot m hx' (α := (x : ℝ))
      (β := (x : ℝ) + D.du) (by linarith) (by push_cast at hmid'; linarith)
    have i2 := intervalIntegrable_f2Integrand (S := S) hGc hiPot m (α := (x : ℝ) + D.du)
      (β := (y : ℝ)) (by linarith) (by push_cast at hmid'; linarith) hy
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    push_cast at ih
    simp only [cost2, List.map_cons, List.sum_cons] at ih ⊢
    linarith

/-! ### The fiber certificate -/

structure FiberCert where
  p4 : List P4Sub
  p2 : List P2Sub
  s4 : Sliver4
  s2 : Sliver2

namespace FiberCert

variable (S : SectorData) (FC : FiberCert)

/-- Contiguity and sliver checks (the subinterval checks are separate theorems). -/
def check : Bool :=
  chain4 0 FC.p4 FC.s4.lo && chain2 FC.s2.hi FC.p2 (1 / 2) && FC.s4.check S && FC.s2.check S

/-- Total dominating matrix. -/
def Qtot : List (List ℚ) := sumMat S.K (FC.p4.map P4Sub.Qhat ++ FC.p2.map P2Sub.Qhat)

/-- Total dominating diagonal. -/
def pertTot (k : ℕ) : ℚ :=
  (FC.p4.map fun D => vecQ D.pertHat k).sum + (FC.p2.map fun D => vecQ D.pertHat k).sum +
    FC.s4.pert S k + FC.s2.pert S k

theorem cost_eq (m : Fin S.K → ℝ) :
    cost4 S.K FC.p4 m + cost2 S.K FC.p2 m + ∑ k : Fin S.K, ((FC.s4.pert S k : ℚ) : ℝ) * m k ^ 2 +
      ∑ k : Fin S.K, ((FC.s2.pert S k : ℚ) : ℝ) * m k ^ 2 =
      quadR S.K (FC.Qtot S) m + ∑ k : Fin S.K, (FC.pertTot S k : ℝ) * m k ^ 2 := by
  have hcost4 : ∀ Ds : List P4Sub, cost4 S.K Ds m = (Ds.map fun D => quadR S.K D.Qhat m).sum +
      ∑ k : Fin S.K, ((Ds.map fun D => vecQ D.pertHat k).sum : ℝ) * m k ^ 2 := by
    intro Ds
    induction Ds with
    | nil => simp [cost4]
    | cons D Ds ih =>
      simp only [cost4, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; push_cast
      simp only [add_mul, Finset.sum_add_distrib]; ring
  have hcost2 : ∀ Ds : List P2Sub, cost2 S.K Ds m = (Ds.map fun D => quadR S.K D.Qhat m).sum +
      ∑ k : Fin S.K, ((Ds.map fun D => vecQ D.pertHat k).sum : ℝ) * m k ^ 2 := by
    intro Ds
    induction Ds with
    | nil => simp [cost2]
    | cons D Ds ih =>
      simp only [cost2, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; push_cast
      simp only [add_mul, Finset.sum_add_distrib]; ring
  rw [hcost4, hcost2, Qtot, quadR_sumMat, List.map_append, List.sum_append, List.map_map,
    List.map_map]
  simp only [pertTot]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, Function.comp_def]
  ring

/-- **Fiberwise floor.** -/
theorem bound (hS : S.valid = true) (hFC : FC.check S = true) (h4 : ∀ D ∈ FC.p4, D.check S = true)
    (h2 : ∀ D ∈ FC.p2, D.check S = true) {G : ℝ → ℝ} (hGc : Continuous G)
    (hiPot : IntegrableOn (fun u => G u ^ 2 * (S.c0 + vTrue u)) (Ioo (0 : ℝ) 1)) :
    2 * quadR S.K S.Λ (S.moments G) - quadR S.K (FC.Qtot S) (S.moments G) -
        ∑ k : Fin S.K, (FC.pertTot S k : ℝ) * S.moments G k ^ 2 ≤
      (∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (S.c0 + vTrue u)) +
        2 * S.e2 * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) +
        2 * S.e3 * (∫ s in (0 : ℝ)..((1 - primeThreeOffset) / 2),
          G (1 - s) * G (primeThreeOffset + s)) := by
  simp only [check, Bool.and_eq_true] at hFC
  obtain ⟨⟨⟨hc4, hc2⟩, hs4⟩, hs2⟩ := hFC
  set m := S.moments G
  set a := primeThreeOffset with ha_def
  obtain ⟨haL, haH⟩ := primeThreeOffset_mem
  have haH1 : (aHiQ : ℝ) ≤ 3 / 5 := by norm_num [aHiQ]
  have haL1 : (1 / 2 : ℝ) ≤ aLoQ := by norm_num [aLoQ]
  -- sliver endpoints
  have hs4' := hs4
  simp only [Sliver4.check, Bool.and_eq_true, decide_eq_true_eq] at hs4'
  have hlo0 : (0 : ℝ) ≤ FC.s4.lo := Rat.cast_nonneg.mpr hs4'.1.1.1
  have hlo1 : (FC.s4.lo : ℝ) ≤ (1 - aHiQ) / 2 := by
    have := Rat.cast_le (K := ℝ).mpr hs4'.1.1.2; push_cast at this; exact this
  have hs2' := hs2
  simp only [Sliver2.check, Bool.and_eq_true, decide_eq_true_eq] at hs2'
  have hhi0 : (1 - aLoQ : ℝ) ≤ FC.s2.hi := by
    have := Rat.cast_le (K := ℝ).mpr hs2'.1.1.1; push_cast at this; exact this
  have hhi1 : (FC.s2.hi : ℝ) ≤ 1 / 2 := by
    have := Rat.cast_le (K := ℝ).mpr hs2'.1.1.2; push_cast at this; exact this
  have hL4 : (FC.s4.lo : ℝ) ≤ (1 - a) / 2 := by linarith only [hlo1, haH]
  -- subinterval and sliver bounds
  have hP4 := integral_chain4 hS hGc hiPot m FC.p4 0 FC.s4.lo hc4 h4 le_rfl hL4
  have hP2 := integral_chain2 hS hGc hiPot m FC.p2 FC.s2.hi (1 / 2) hc2 h2
    (by have : (0 : ℝ) ≤ FC.s2.hi := by linarith only [hhi0, haL, haL1, haH, haH1]
        exact Rat.cast_nonneg.mp this) (by push_cast; norm_num)
  push_cast at hP4 hP2
  have hT4 := Sliver4.bound hS hs4 hGc hiPot m
  have hT2 := Sliver2.bound hS hs2 hGc hiPot m
  -- splitting the fiber integrals at the sliver endpoints
  have hf4a := intervalIntegrable_f4Integrand (S := S) hGc hiPot m le_rfl hlo0 (by linarith only [hL4])
  have hf4b := intervalIntegrable_f4Integrand (S := S) hGc hiPot m hlo0 hL4 le_rfl
  have hf2a' := intervalIntegrable_f2Integrand (S := S) hGc hiPot m (α := 1 - a) (β := FC.s2.hi)
    (by linarith only [haH, haH1]) (by linarith only [hhi0, haL]) (by linarith only [hhi1])
  have hf2b := intervalIntegrable_f2Integrand (S := S) hGc hiPot m (α := FC.s2.hi) (β := 1 / 2)
    (by linarith only [hhi0, haL, haH, haH1]) hhi1 (by norm_num)
  have hsplit4 := intervalIntegral.integral_add_adjacent_intervals hf4a hf4b
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hf2a' hf2b
  -- folding of the potential part and of the prime-two contact
  have hpc : Continuous (S.phiFn m) :=
    continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_qeval _)
  set H : ℝ → ℝ := fun u => G u ^ 2 * (S.c0 + vTrue u) - 2 * (G u * S.phiFn m u)
  have hiPhi : IntegrableOn (fun u => G u * S.phiFn m u) (Ioo (0 : ℝ) 1) :=
    (hGc.mul hpc).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiH : IntegrableOn H (Ioo (0 : ℝ) 1) := hiPot.sub (hiPhi.const_mul 2)
  have hH : (∫ u in Ioo (0 : ℝ) 1, H u) =
      (∫ u in Ioo (0 : ℝ) 1, G u ^ 2 * (S.c0 + vTrue u)) - 2 * quadR S.K S.Λ m := by
    have hpair := SectorData.integral_mul_phiFn hS hGc
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hpair
    simp only [H]
    rw [integral_sub hiPot (hiPhi.const_mul 2), integral_const_mul, hpair]
  have hFold := six_interval_folding_diag hiH
  have hFoldP2 := six_interval_folding_primeTwo hGc
  simp only at hFold hFoldP2
  rw [← ha_def] at hFold hFoldP2 hT4 hT2
  have hp4c : Continuous fun s => G s * G (1 - s) + G (a + s) * G (1 - a - s) := by fun_prop
  have hp3c : Continuous fun s => G (1 - s) * G (a + s) := by fun_prop
  have hp2c : Continuous fun u => G u * G (1 - u) := by fun_prop
  have hf4full := intervalIntegrable_f4Integrand (S := S) hGc hiPot m le_rfl
    (by linarith only [hlo0, hL4] : (0 : ℝ) ≤ (1 - a) / 2) le_rfl
  have hf2full := intervalIntegrable_f2Integrand (S := S) hGc hiPot m (α := 1 - a) (β := 1 / 2)
    (by linarith only [haH, haH1]) (by linarith only [haL, haL1]) (by norm_num)
  have hI4 : (∫ s in (0 : ℝ)..((1 - a) / 2), H s + H (1 - s) + H (a + s) + H (1 - a - s)) =
      (∫ s in (0 : ℝ)..((1 - a) / 2), f4Integrand S G m s) -
        2 * S.e2 * (∫ s in (0 : ℝ)..((1 - a) / 2), G s * G (1 - s) + G (a + s) * G (1 - a - s)) -
        2 * S.e3 * (∫ s in (0 : ℝ)..((1 - a) / 2), G (1 - s) * G (a + s)) := by
    have hfn : (fun s => H s + H (1 - s) + H (a + s) + H (1 - a - s)) = fun s =>
        (f4Integrand S G m s - 2 * S.e2 * (G s * G (1 - s) + G (a + s) * G (1 - a - s))) -
          2 * S.e3 * (G (1 - s) * G (a + s)) := by
      funext s; simp only [H, f4Integrand, tridiag4Form, ha_def]; ring
    rw [hfn, intervalIntegral.integral_sub (hf4full.sub ((hp4c.const_mul _).intervalIntegrable _ _))
      ((hp3c.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_sub hf4full ((hp4c.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hI2 : (∫ u in (1 - a)..(1 / 2), H u + H (1 - u)) =
      (∫ u in (1 - a)..(1 / 2), f2Integrand S G m u) -
        2 * S.e2 * (∫ u in (1 - a)..(1 / 2), G u * G (1 - u)) := by
    have hfn : (fun u => H u + H (1 - u)) = fun u =>
        f2Integrand S G m u - 2 * S.e2 * (G u * G (1 - u)) := by
      funext u; simp only [H, f2Integrand, tridiag2Form]; ring
    rw [hfn, intervalIntegral.integral_sub hf2full ((hp2c.const_mul _).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
  have hFoldP2' : 2 * (S.e2 : ℝ) * (∫ u in (0 : ℝ)..(1 / 2), G u * G (1 - u)) =
      2 * (S.e2 : ℝ) *
          (∫ s in (0 : ℝ)..((1 - a) / 2), G s * G (1 - s) + G (a + s) * G (1 - a - s)) +
        2 * (S.e2 : ℝ) * (∫ u in (1 - a)..(1 / 2), G u * G (1 - u)) := by
    rw [hFoldP2, mul_add]
  have hcost := cost_eq S FC m
  push_cast at hcost
  linarith only [hH, hFold, hFoldP2', hI4, hI2, hsplit4, hsplit2, hP4, hP2, hT4, hT2, hcost]

end FiberCert

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
