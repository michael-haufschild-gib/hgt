import GaloisForLFunctions.RHTower.CharacterSumMeanValue
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare

open Complex MeasureTheory Set Finset

noncomputable section

namespace RHTower.Sieve

/-- One residue class occupies at most `length / e + 1` points of a half-open interval. -/
theorem card_residue_Ioc_le {e : ℕ} (_he : 0 < e) (A B r : ℕ) :
    ((((Finset.Ioc A B).filter (fun m => m % e = r)).card : ℕ) : ℝ)
      ≤ ((B - A : ℕ) : ℝ) / (e : ℝ) + 1 := by
  classical
  set F : Finset ℕ := (Finset.Ioc A B).filter (fun m => m % e = r) with hF
  have hmap : ∀ m ∈ F, (m - A) / e ∈ Finset.range ((B - A) / e + 1) := by
    intro m hm
    rw [hF, Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [Finset.mem_range]
    have hsub : m - A ≤ B - A := Nat.sub_le_sub_right hm.1.2 A
    have hdiv : (m - A) / e ≤ (B - A) / e := Nat.div_le_div_right hsub
    omega
  have hinj : Set.InjOn (fun m => (m - A) / e) ↑F := by
    intro m hm n hn hq
    simp only [Finset.mem_coe] at hm hn
    rw [hF, Finset.mem_filter, Finset.mem_Ioc] at hm hn
    have hmod : m ≡ n [MOD e] := by
      exact hm.2.trans hn.2.symm
    have hsubmod : m - A ≡ n - A [MOD e] :=
      Nat.ModEq.sub_right hm.1.1.le hn.1.1.le hmod
    have hdecomp_m := Nat.div_add_mod (m - A) e
    have hdecomp_n := Nat.div_add_mod (n - A) e
    have hsubeq : m - A = n - A := by
      change (m - A) / e = (n - A) / e at hq
      change (m - A) % e = (n - A) % e at hsubmod
      calc
        m - A = e * ((m - A) / e) + (m - A) % e := hdecomp_m.symm
        _ = e * ((n - A) / e) + (n - A) % e := by rw [hq, hsubmod]
        _ = n - A := hdecomp_n
    omega
  have hcard : F.card ≤ (Finset.range ((B - A) / e + 1)).card :=
    Finset.card_le_card_of_injOn (fun m => (m - A) / e) hmap hinj
  rw [Finset.card_range] at hcard
  have hcast : (F.card : ℝ) ≤ (((B - A) / e : ℕ) : ℝ) + 1 := by
    exact_mod_cast hcard
  have hdiv : (((B - A) / e : ℕ) : ℝ) ≤ ((B - A : ℕ) : ℝ) / (e : ℝ) :=
    Nat.cast_div_le
  rw [hF]
  nlinarith

/-- A logarithmic neighbor window inside one residue class gains the reciprocal modulus. -/
theorem logNeighbourCount_residue_le (s : Finset ℕ) {e : ℕ} (he : 0 < e) (r : ℕ)
    (hs0 : (0 : ℕ) ∉ s) (hres : ∀ m ∈ s, m % e = r) {δ : ℝ} (hδ : 0 ≤ δ) {n : ℕ}
    (hn : 1 ≤ n) :
    (logNeighbourCount s δ n : ℝ)
      ≤ (n : ℝ) * (Real.exp δ - Real.exp (-δ)) / (e : ℝ) + 2 := by
  classical
  let A := ⌊(n : ℝ) * Real.exp (-δ)⌋₊
  let B := ⌊(n : ℝ) * Real.exp δ⌋₊
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexp : Real.exp (-δ) ≤ Real.exp δ := Real.exp_le_exp.2 (by linarith)
  have hAB : A ≤ B := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hexp hnR.le)
  have hsub : (s.filter fun m : ℕ => |Real.log (n : ℝ) - Real.log (m : ℝ)| < δ)
      ⊆ (Finset.Ioc A B).filter (fun m => m % e = r) := by
    intro m hm
    obtain ⟨hms, hlog⟩ := Finset.mem_filter.1 hm
    have hm1 : 0 < m := Nat.pos_of_ne_zero fun h => hs0 (h ▸ hms)
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    rw [abs_lt] at hlog
    have hupper : (m : ℝ) < (n : ℝ) * Real.exp δ := by
      have h := Real.exp_lt_exp.2
        (show Real.log (m : ℝ) - Real.log (n : ℝ) < δ by linarith [hlog.1])
      rw [Real.exp_sub, Real.exp_log hmR, Real.exp_log hnR, div_lt_iff₀ hnR] at h
      linarith
    have hlower : (n : ℝ) * Real.exp (-δ) < (m : ℝ) := by
      have h := Real.exp_lt_exp.2 hlog.2
      rw [Real.exp_sub, Real.exp_log hnR, Real.exp_log hmR, div_lt_iff₀ hmR] at h
      have hprod : Real.exp δ * Real.exp (-δ) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [h, Real.exp_pos (-δ), hprod]
    exact Finset.mem_filter.2
      ⟨Finset.mem_Ioc.2
        ⟨(Nat.floor_lt (by positivity)).2 hlower, Nat.le_floor hupper.le⟩, hres m hms⟩
  have hcard := Finset.card_le_card hsub
  have hcount : (logNeighbourCount s δ n : ℝ)
      ≤ (((Finset.Ioc A B).filter (fun m => m % e = r)).card : ℝ) := by
    rw [logNeighbourCount]
    exact_mod_cast hcard
  have hrescard := card_residue_Ioc_le he A B r
  have hfloor : ((B - A : ℕ) : ℝ)
      ≤ (n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1 := by
    rw [Nat.cast_sub hAB]
    have hB : (B : ℝ) ≤ (n : ℝ) * Real.exp δ := Nat.floor_le (by positivity)
    have hA0 : (n : ℝ) * Real.exp (-δ) < (A : ℝ) + 1 := by
      simpa only [A] using Nat.lt_floor_add_one ((n : ℝ) * Real.exp (-δ))
    have hA : (n : ℝ) * Real.exp (-δ) - 1 < (A : ℝ) := by linarith
    linarith
  have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  calc
    (logNeighbourCount s δ n : ℝ)
        ≤ (((Finset.Ioc A B).filter (fun m => m % e = r)).card : ℝ) := hcount
    _ ≤ ((B - A : ℕ) : ℝ) / (e : ℝ) + 1 := hrescard
    _ ≤ ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) + 1) / (e : ℝ) + 1 := by
      gcongr
    _ ≤ (n : ℝ) * (Real.exp δ - Real.exp (-δ)) / (e : ℝ) + 2 := by
      have hone : 1 / (e : ℝ) ≤ 1 := by rw [div_le_one hepos]; exact heR
      ring_nf at hone ⊢
      linarith

/-- Gallagher mean square for coefficients supported on one residue class. -/
theorem integral_Icc_normSq_logPoly_le_residue (a : ℕ → ℂ) (s : Finset ℕ)
    {e : ℕ} (he : 0 < e) (r : ℕ) (hs0 : (0 : ℕ) ∉ s)
    (hres : ∀ n ∈ s, n % e = r) {δ W : ℝ} (hδ : 0 < δ)
    (hWδ : 2 * Real.pi * δ * W ≤ 1) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ (5 / (4 * δ)) * ∑ n ∈ s,
        ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / (e : ℝ) + 2) * ‖a n‖ ^ 2 := by
  refine le_trans (integral_Icc_normSq_logPoly_le_count a s hδ hWδ) ?_
  have hfac : (0 : ℝ) ≤ 5 / (4 * δ) := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) hfac
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h => hs0 (h ▸ hn)
  exact mul_le_mul_of_nonneg_right
    (logNeighbourCount_residue_le s he r hs0 hres hδ.le hn1) (by positivity)

/-- Affine mean square for a finite Dirichlet series supported on one residue class.
The height-independent mass gains a full reciprocal modulus. -/
theorem integral_Icc_normSq_LSeries_le_residue_affine {a : ℕ → ℂ} {s : Finset ℕ}
    {e : ℕ} (he : 0 < e) (r : ℕ) (hs0 : (0 : ℕ) ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hres : ∀ n ∈ s, n % e = r)
    (σ : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in Set.Icc (-T) T, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ (5 * Real.pi * Real.exp 1 / (e : ℝ)) *
          ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
        + 5 * Real.pi * T *
          ∑ n ∈ s, ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hδ : (0 : ℝ) < 1 / T := by positivity
  have hWδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    rw [show 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 by field_simp]
  rw [integral_Icc_normSq_LSeries_eq hs0 hsupp σ hT0.le]
  refine le_trans (mul_le_mul_of_nonneg_left
    (integral_Icc_normSq_logPoly_le_residue
      (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s he r hs0 hres hδ hWδ)
    (by positivity)) ?_
  have hwindow := mul_exp_sub_exp_neg_le hT
  set E0 : ℝ := ∑ n ∈ s, ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 with hE0def
  set E1 : ℝ := ∑ n ∈ s, (n : ℝ) * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 with hE1def
  have hE0 : 0 ≤ E0 := by
    rw [hE0def]
    exact Finset.sum_nonneg fun n _ => by positivity
  have hE1 : 0 ≤ E1 := by
    rw [hE1def]
    exact Finset.sum_nonneg fun n _ => by positivity
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hsplit : ∑ n ∈ s,
      ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) / (e : ℝ) + 2) *
        ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2
      = (Real.exp (1 / T) - Real.exp (-(1 / T))) / (e : ℝ) *
          E1 + 2 * E0 := by
    rw [hE0def, hE1def]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    ring
  rw [hsplit]
  have hmain : T * (Real.exp (1 / T) - Real.exp (-(1 / T))) / (e : ℝ) * E1
      ≤ (2 * Real.exp 1 / (e : ℝ)) * E1 := by
    have := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hwindow heR.le) hE1
    simpa [mul_assoc] using this
  have hcoef : 2 * Real.pi * (5 / (4 * (1 / T))) = 5 * Real.pi * T / 2 := by
    field_simp
    ring
  rw [← mul_assoc, hcoef]
  calc
    5 * Real.pi * T / 2 *
          ((Real.exp (1 / T) - Real.exp (-(1 / T))) / (e : ℝ) * E1 + 2 * E0)
        = (5 * Real.pi / 2) *
            (T * (Real.exp (1 / T) - Real.exp (-(1 / T))) / (e : ℝ) * E1)
          + 5 * Real.pi * T * E0 := by ring
    _ ≤ (5 * Real.pi / 2) * ((2 * Real.exp 1 / (e : ℝ)) * E1)
          + 5 * Real.pi * T * E0 := by
      have hscaled : (5 * Real.pi / 2) *
            (T * (Real.exp (1 / T) - Real.exp (-(1 / T))) / (e : ℝ) * E1)
          ≤ (5 * Real.pi / 2) * ((2 * Real.exp 1 / (e : ℝ)) * E1) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
      exact add_le_add hscaled (le_refl (5 * Real.pi * T * E0))
    _ = 5 * Real.pi * Real.exp 1 / (e : ℝ) * E1 + 5 * Real.pi * T * E0 := by ring

/-- The finite interval inside the reduced residue class represented by `u`. -/
def characterResidueInterval (q N : ℕ) (u : (ZMod (q + 1))ˣ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun n : ℕ => (Nat.cast n : ZMod (q + 1)) = (u : ZMod (q + 1)))

/-- Character-twisted Gallagher polynomial on `[1,N]`. -/
noncomputable def characterLogPoly (q N : ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ (q + 1)) (w : ℝ) : ℂ :=
  charSum q N
    (fun n => a n * Complex.exp
      (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I)) χ

theorem continuous_characterLogPoly (q N : ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ (q + 1)) :
    Continuous (characterLogPoly q N a χ) := by
  unfold characterLogPoly charSum
  refine continuous_finsetSum _ fun n _ => ?_
  exact (continuous_const.mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const))).mul continuous_const

/-- Character orthogonality turns the full family square into residue-fibre squares pointwise. -/
theorem sum_normSq_characterLogPoly (q N : ℕ) (a : ℕ → ℂ) (w : ℝ) :
    ∑ χ : DirichletCharacter ℂ (q + 1), ‖characterLogPoly q N a χ w‖ ^ 2
      = ((q + 1).totient : ℝ) *
        ∑ u : (ZMod (q + 1))ˣ, ‖logPoly a (characterResidueInterval q N u) w‖ ^ 2 := by
  let b : ℕ → ℂ := fun n => a n * Complex.exp
    (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I)
  have hbase := sum_normSq_charSum q N b
  have hchar : ∀ χ : DirichletCharacter ℂ (q + 1),
      charSum q N b χ = characterLogPoly q N a χ w := by
    intro χ
    rfl
  have hclass : ∀ u : (ZMod (q + 1))ˣ,
      classSum q N b u = logPoly a (characterResidueInterval q N u) w := by
    intro u
    unfold classSum logPoly characterResidueInterval b
    refine Finset.sum_congr rfl fun n hn => ?_
    ring
  simpa only [hchar, hclass] using hbase

/-- Full-character continuous hybrid mean square. Character orthogonality and residue sparsity
combine to replace the naive `qN` term by `N`; only the time term retains the family size. -/
theorem sum_integral_normSq_characterLogPoly_le (q N : ℕ) (a : ℕ → ℂ)
    {δ W : ℝ} (hδ : 0 < δ) (hWδ : 2 * Real.pi * δ * W ≤ 1) :
    ∑ χ : DirichletCharacter ℂ (q + 1),
        (∫ w in Set.Icc (-W) W, ‖characterLogPoly q N a χ w‖ ^ 2)
      ≤ ((q + 1).totient : ℝ) * (5 / (4 * δ)) *
        ∑ n ∈ Finset.Icc 1 N,
          ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
            ‖a n‖ ^ 2 := by
  classical
  let I : Set ℝ := Set.Icc (-W) W
  have hχint : ∀ χ : DirichletCharacter ℂ (q + 1),
      Integrable (fun w => ‖characterLogPoly q N a χ w‖ ^ 2) (volume.restrict I) := by
    intro χ
    exact (continuous_characterLogPoly q N a χ).norm.pow 2 |>.integrableOn_Icc
  have huiles : ∀ u : (ZMod (q + 1))ˣ,
      Integrable (fun w => ‖logPoly a (characterResidueInterval q N u) w‖ ^ 2)
        (volume.restrict I) := by
    intro u
    exact (continuous_logPoly a (characterResidueInterval q N u)).norm.pow 2
      |>.integrableOn_Icc
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun χ _ => hχint χ)]
  have hpoint : ∀ w : ℝ,
      (∑ χ : DirichletCharacter ℂ (q + 1), ‖characterLogPoly q N a χ w‖ ^ 2)
        = ((q + 1).totient : ℝ) *
          ∑ u : (ZMod (q + 1))ˣ, ‖logPoly a (characterResidueInterval q N u) w‖ ^ 2 :=
    sum_normSq_characterLogPoly q N a
  change (∫ w in I, ∑ χ : DirichletCharacter ℂ (q + 1),
      ‖characterLogPoly q N a χ w‖ ^ 2) ≤ _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun w _ => hpoint w)]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun u _ => huiles u)]
  have hu_bound : ∀ u : (ZMod (q + 1))ˣ,
      (∫ w in I, ‖logPoly a (characterResidueInterval q N u) w‖ ^ 2)
        ≤ (5 / (4 * δ)) * ∑ n ∈ characterResidueInterval q N u,
          ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
            ‖a n‖ ^ 2 := by
    intro u
    have hs0 : (0 : ℕ) ∉ characterResidueInterval q N u := by
      simp [characterResidueInterval]
    have hres : ∀ n ∈ characterResidueInterval q N u, n % (q + 1) = (u : ZMod (q + 1)).val := by
      intro n hn
      have hcast := (Finset.mem_filter.1 hn).2
      rw [← ZMod.val_natCast, hcast]
    exact integral_Icc_normSq_logPoly_le_residue a (characterResidueInterval q N u)
      (by omega : 0 < q + 1) (u : ZMod (q + 1)).val hs0 hres hδ hWδ
  have hsum_bound :
      ∑ u : (ZMod (q + 1))ˣ, (∫ w in I,
        ‖logPoly a (characterResidueInterval q N u) w‖ ^ 2)
      ≤ ∑ u : (ZMod (q + 1))ˣ, (5 / (4 * δ)) *
        ∑ n ∈ characterResidueInterval q N u,
          ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
            ‖a n‖ ^ 2 := Finset.sum_le_sum fun u _ => hu_bound u
  have hfac0 : (0 : ℝ) ≤ ((q + 1).totient : ℝ) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum_bound hfac0) ?_
  let g : ℕ → ℝ := fun n =>
    ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) * ‖a n‖ ^ 2
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    unfold g
    have hexp : 0 ≤ Real.exp δ - Real.exp (-δ) := by
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
    positivity
  have hfib : ∑ u : (ZMod (q + 1))ˣ, ∑ n ∈ characterResidueInterval q N u, g n
      ≤ ∑ n ∈ Finset.Icc 1 N, g n := by
    have hcomplex := sum_over_units_fibers q N (fun n => ((g n : ℝ) : ℂ))
    have hreal := congrArg Complex.re hcomplex
    simp only [Complex.ofReal_re, Complex.re_sum, apply_ite, Complex.zero_re] at hreal
    rw [show (∑ u : (ZMod (q + 1))ˣ, ∑ n ∈ characterResidueInterval q N u, g n) =
        ∑ n ∈ Finset.Icc 1 N, if IsUnit (Nat.cast n : ZMod (q + 1)) then g n else 0 by
      simpa only [characterResidueInterval] using hreal]
    exact Finset.sum_le_sum fun n hn => by
      split_ifs <;> simp [hg0 n]
  dsimp [g] at hfib
  have hδfac : (0 : ℝ) ≤ 5 / (4 * δ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hfib (mul_nonneg hfac0 hδfac)
  calc
    ((q + 1).totient : ℝ) *
          ∑ u : (ZMod (q + 1))ˣ, (5 / (4 * δ)) *
            ∑ n ∈ characterResidueInterval q N u,
              ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
                ‖a n‖ ^ 2
        = (((q + 1).totient : ℝ) * (5 / (4 * δ))) *
            ∑ u : (ZMod (q + 1))ˣ, ∑ n ∈ characterResidueInterval q N u,
              ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
                ‖a n‖ ^ 2 := by
          rw [← Finset.mul_sum]
          ring
    _ ≤ (((q + 1).totient : ℝ) * (5 / (4 * δ))) *
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
              ‖a n‖ ^ 2 := hscaled
    _ = ((q + 1).totient : ℝ) * (5 / (4 * δ)) *
          ∑ n ∈ Finset.Icc 1 N,
            ((n : ℝ) * (Real.exp δ - Real.exp (-δ)) / ((q + 1 : ℕ) : ℝ) + 2) *
              ‖a n‖ ^ 2 := by ring

/-- Affine hybrid mean square on the natural height scale. The character-family factor cancels
from the coefficient-length term; it remains only in the height term. -/
theorem sum_integral_normSq_characterLogPoly_le_affine (q N : ℕ) (a : ℕ → ℂ)
    {T : ℝ} (hT : 1 ≤ T) :
    ∑ χ : DirichletCharacter ℂ (q + 1),
        (∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
          ‖characterLogPoly q N a χ w‖ ^ 2)
      ≤ (5 * Real.exp 1 / 2) *
          ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2
        + (5 / 2) * ((q + 1).totient : ℝ) * T *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hδ : (0 : ℝ) < 1 / T := by positivity
  have hWδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    rw [show 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 by field_simp]
  refine le_trans (sum_integral_normSq_characterLogPoly_le q N a hδ hWδ) ?_
  set E0 : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 with hE0def
  set E1 : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2 with hE1def
  have hE0 : 0 ≤ E0 := by
    rw [hE0def]
    exact Finset.sum_nonneg fun n _ => by positivity
  have hE1 : 0 ≤ E1 := by
    rw [hE1def]
    exact Finset.sum_nonneg fun n _ => by positivity
  have hsplit : ∑ n ∈ Finset.Icc 1 N,
      ((n : ℝ) * (Real.exp (1 / T) - Real.exp (-(1 / T))) / ((q + 1 : ℕ) : ℝ) + 2) *
        ‖a n‖ ^ 2
      = (Real.exp (1 / T) - Real.exp (-(1 / T))) / ((q + 1 : ℕ) : ℝ) * E1
        + 2 * E0 := by
    rw [hE0def, hE1def, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit]
  have hwindow := mul_exp_sub_exp_neg_le hT
  have hratio : ((q + 1).totient : ℝ) / ((q + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.totient_le (q + 1)
  have hratio0 : 0 ≤ ((q + 1).totient : ℝ) / ((q + 1 : ℕ) : ℝ) := by positivity
  have hprod : T * (Real.exp (1 / T) - Real.exp (-(1 / T))) *
      (((q + 1).totient : ℝ) / ((q + 1 : ℕ) : ℝ)) ≤ 2 * Real.exp 1 := by
    calc
      T * (Real.exp (1 / T) - Real.exp (-(1 / T))) *
          (((q + 1).totient : ℝ) / ((q + 1 : ℕ) : ℝ))
        ≤ (2 * Real.exp 1) * (((q + 1).totient : ℝ) / ((q + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hwindow hratio0
      _ ≤ (2 * Real.exp 1) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * Real.exp 1 := by ring
  have hcoef : 5 / (4 * (1 / T)) = 5 * T / 4 := by field_simp
  rw [hcoef]
  have hmain : ((q + 1).totient : ℝ) * (5 * T / 4) *
      ((Real.exp (1 / T) - Real.exp (-(1 / T))) / ((q + 1 : ℕ) : ℝ) * E1)
      ≤ (5 * Real.exp 1 / 2) * E1 := by
    have hscaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 5 / 4)) hE1
    calc
      ((q + 1).totient : ℝ) * (5 * T / 4) *
          ((Real.exp (1 / T) - Real.exp (-(1 / T))) / ((q + 1 : ℕ) : ℝ) * E1)
        = (5 / 4) * (T * (Real.exp (1 / T) - Real.exp (-(1 / T))) *
            (((q + 1).totient : ℝ) / ((q + 1 : ℕ) : ℝ))) * E1 := by ring
      _ ≤ (5 / 4) * (2 * Real.exp 1) * E1 := hscaled
      _ = (5 * Real.exp 1 / 2) * E1 := by ring
  calc
    ((q + 1).totient : ℝ) * (5 * T / 4) *
          ((Real.exp (1 / T) - Real.exp (-(1 / T))) / ((q + 1 : ℕ) : ℝ) * E1 + 2 * E0)
        = ((q + 1).totient : ℝ) * (5 * T / 4) *
            ((Real.exp (1 / T) - Real.exp (-(1 / T))) / ((q + 1 : ℕ) : ℝ) * E1)
          + (5 / 2) * ((q + 1).totient : ℝ) * T * E0 := by ring
    _ ≤ (5 * Real.exp 1 / 2) * E1 +
          (5 / 2) * ((q + 1).totient : ℝ) * T * E0 :=
      add_le_add hmain (le_refl _)

/-- Closed `(N + φ(q)T)` form of the continuous hybrid large sieve. -/
theorem sum_integral_normSq_characterLogPoly_le_length (q N : ℕ) (a : ℕ → ℂ)
    {T : ℝ} (hT : 1 ≤ T) :
    ∑ χ : DirichletCharacter ℂ (q + 1),
        (∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
          ‖characterLogPoly q N a χ w‖ ^ 2)
      ≤ ((5 * Real.exp 1 / 2) * (N : ℝ) +
          (5 / 2) * ((q + 1).totient : ℝ) * T) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  refine le_trans (sum_integral_normSq_characterLogPoly_le_affine q N a hT) ?_
  have hweighted : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.1 hn).2) (by positivity)
  have hfac : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hweighted hfac
  calc
    (5 * Real.exp 1 / 2) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖a n‖ ^ 2
          + (5 / 2) * ((q + 1).totient : ℝ) * T *
            ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
        ≤ (5 * Real.exp 1 / 2) *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)
          + (5 / 2) * ((q + 1).totient : ℝ) * T *
            ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := add_le_add hscaled (le_refl _)
    _ = ((5 * Real.exp 1 / 2) * (N : ℝ) +
          (5 / 2) * ((q + 1).totient : ℝ) * T) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring

end RHTower.Sieve
