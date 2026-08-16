import GaloisForLFunctions.RHTower.SuzukiLatticeShellWeight

/-!
# `(17)`: the polynomial group estimate, with the sharp exponent

Conjugating the evolution by the shell weight of degree `m` costs exactly `m` powers of the time:
the shell weight is dominated by the coordinate moments of order `m`, each of those is controlled by
the sharp moment bound, and every moment of order at most `m` of the initial field is dominated by
its shell-weighted norm.
-/

open Finset

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

omit [Fintype P] [DecidableEq P] in
theorem memℓp_of_norm_le {f : (P → ℤ) → ℂ} {u : H}
    (h : ∀ r, ‖f r‖ ≤ ‖((u : H) : (P → ℤ) → ℂ) r‖) : Memℓp f 2 := by
  refine memℓp_gen ?_
  refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
    ((memℓp_gen_iff (p := 2) (by norm_num)).mp (lp.memℓp u))
  exact Real.rpow_le_rpow (norm_nonneg _) (h r) (by norm_num)

set_option maxHeartbeats 1000000 in
omit [DecidableEq P] in
/-- **`(17)`: the polynomial group estimate.** -/
theorem exists_norm_shellWeighted_exp_le {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (g : (P → ℤ) → ℂ) (hg : (Function.support g).Finite),
      ∃ v : H, ((v : H) : (P → ℤ) → ℂ) = shellWeightField m
          ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
              (l2OfFinSupp g hg) : H) : (P → ℤ) → ℂ)
        ∧ ‖v‖ ≤ C * (1 + |x|) ^ m
            * ‖(l2OfFinSupp (shellWeightField m g)
                (hg.subset (support_shellWeightField_subset m g)) : H)‖ := by
  classical
  choose Cf hCf hbf using fun p : P => exists_sharp_moment_bound hsa p m
  set K : ℝ := ((Fintype.card P : ℝ) + 1) ^ m with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨K * (1 + ∑ p, Cf p), by
    have : (0 : ℝ) ≤ ∑ p, Cf p := Finset.sum_nonneg fun p _ => hCf p
    positivity, fun x g hg => ?_⟩
  set u : H := NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
    (l2OfFinSupp g hg) with hudef
  set M : ℝ := ‖(l2OfFinSupp (shellWeightField m g)
    (hg.subset (support_shellWeightField_subset m g)) : H)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  -- the moment vectors of the evolution
  have hmom : ∀ p : P, ∃ w : H, ((w : H) : (P → ℤ) → ℂ)
      = posPowField p m ((u : H) : (P → ℤ) → ℂ) ∧ ‖w‖ ≤ Cf p * (1 + |x|) ^ m * M := by
    intro p
    refine hbf p x g hg M ?_
    intro i hi
    exact norm_posPow_le_shellWeighted (Finset.mem_range.mp hi |> Nat.lt_succ_iff.mp) p hg
  choose w hw hwn using hmom
  -- the majorant
  set maj : H := (K : ℂ) • (absL2 u + ∑ p, absL2 (w p)) with hmajdef
  have hmajval : ∀ r : P → ℤ, ‖((maj : H) : (P → ℤ) → ℂ) r‖
      = K * (‖((u : H) : (P → ℤ) → ℂ) r‖ + ∑ p, ‖((w p : H) : (P → ℤ) → ℂ) r‖) := by
    intro r
    rw [hmajdef, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hK]
    congr 1
    rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply, coe_absL2]
    have hre : ∀ p : P, ((absL2 (w p) : H) : (P → ℤ) → ℂ) r
        = ((‖((w p : H) : (P → ℤ) → ℂ) r‖ : ℝ) : ℂ) := fun p => coe_absL2 (w p) r
    rw [Finset.sum_congr rfl (fun p _ => hre p)]
    rw [show (((‖((u : H) : (P → ℤ) → ℂ) r‖ : ℝ) : ℂ)
        + ∑ p, ((‖((w p : H) : (P → ℤ) → ℂ) r‖ : ℝ) : ℂ))
      = (((‖((u : H) : (P → ℤ) → ℂ) r‖ + ∑ p, ‖((w p : H) : (P → ℤ) → ℂ) r‖ : ℝ)) : ℂ) by
        push_cast
        ring]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hdom : ∀ r : P → ℤ, ‖shellWeightField m ((u : H) : (P → ℤ) → ℂ) r‖
      ≤ ‖((maj : H) : (P → ℤ) → ℂ) r‖ := by
    intro r
    rw [hmajval r, shellWeightField, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (shellWeight_pos m r).le]
    have hshell : shellWeight m r ≤ K * (1 + ∑ p, |((r p : ℤ) : ℝ)| ^ m) := by
      cases m with
      | zero =>
        rw [shellWeight, pow_zero, hKdef, pow_zero, one_mul]
        have : (0 : ℝ) ≤ ∑ p, |((r p : ℤ) : ℝ)| ^ 0 := by positivity
        linarith
      | succ k =>
        have hbase := orbitLength_pow_le (P := P) k r
        rw [shellWeight, hKdef]
        refine le_trans hbase ?_
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine pow_le_pow_right₀ ?_ (by omega)
        have : (0 : ℝ) ≤ (Fintype.card P : ℝ) := by positivity
        linarith
    have hwval : ∀ p : P, ‖((w p : H) : (P → ℤ) → ℂ) r‖
        = |((r p : ℤ) : ℝ)| ^ m * ‖((u : H) : (P → ℤ) → ℂ) r‖ := by
      intro p
      rw [congrFun (hw p) r, posPowField, norm_mul, norm_pow]
      congr 2
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    rw [Finset.sum_congr rfl (fun p _ => hwval p)]
    have hu0 : (0 : ℝ) ≤ ‖((u : H) : (P → ℤ) → ℂ) r‖ := norm_nonneg _
    calc shellWeight m r * ‖((u : H) : (P → ℤ) → ℂ) r‖
        ≤ (K * (1 + ∑ p, |((r p : ℤ) : ℝ)| ^ m)) * ‖((u : H) : (P → ℤ) → ℂ) r‖ :=
          mul_le_mul_of_nonneg_right hshell hu0
      _ = K * (‖((u : H) : (P → ℤ) → ℂ) r‖
            + ∑ p, |((r p : ℤ) : ℝ)| ^ m * ‖((u : H) : (P → ℤ) → ℂ) r‖) := by
          rw [← Finset.sum_mul]
          ring
  refine ⟨⟨shellWeightField m ((u : H) : (P → ℤ) → ℂ), memℓp_of_norm_le hdom⟩, rfl, ?_⟩
  have hvle : ‖(⟨shellWeightField m ((u : H) : (P → ℤ) → ℂ), memℓp_of_norm_le hdom⟩ : H)‖
      ≤ ‖maj‖ := norm_le_of_pointwise_le hdom
  refine le_trans hvle ?_
  have hun : ‖u‖ ≤ M := by
    rw [hudef, norm_exp_latticeAdjacency_apply hsa x]
    refine norm_le_of_pointwise_le fun r => ?_
    rw [coe_l2OfFinSupp, coe_l2OfFinSupp, shellWeightField, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (shellWeight_pos m r).le]
    nlinarith [one_le_shellWeight m r, norm_nonneg (g r)]
  have hmajn : ‖maj‖ ≤ K * (‖u‖ + ∑ p, ‖w p‖) := by
    rw [hmajdef, norm_smul, Complex.norm_real, Real.norm_of_nonneg hK]
    refine mul_le_mul_of_nonneg_left ?_ hK
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_of_eq (norm_absL2 u)) ?_
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun p _ => le_of_eq (norm_absL2 (w p))
  refine le_trans hmajn ?_
  have hsum : ∑ p, ‖w p‖ ≤ (∑ p, Cf p) * (1 + |x|) ^ m * M := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum fun p _ => hwn p
  have hpow : (1 : ℝ) ≤ (1 + |x|) ^ m := by
    refine one_le_pow₀ ?_
    have := abs_nonneg x
    linarith
  have hCsum : (0 : ℝ) ≤ ∑ p, Cf p := Finset.sum_nonneg fun p _ => hCf p
  calc K * (‖u‖ + ∑ p, ‖w p‖)
      ≤ K * (M + (∑ p, Cf p) * (1 + |x|) ^ m * M) :=
        mul_le_mul_of_nonneg_left (add_le_add hun hsum) hK
    _ ≤ K * (1 + ∑ p, Cf p) * (1 + |x|) ^ m * M := by
        have hMle : M ≤ (1 + |x|) ^ m * M := by nlinarith [hpow, hM0]
        nlinarith [hMle, hK, hCsum, hM0, hpow,
          mul_nonneg hK (mul_nonneg hCsum hM0)]

end RHTower
