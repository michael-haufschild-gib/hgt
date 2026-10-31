import GaloisForLFunctions.RenormalizedIntersectionTheory.TheKunnethSquareOfWeilsKernelIsRH

/-!
# The Hadamard powers of Weil's kernel

The **Hadamard powers** `u ↦ K(u)^n` are the restrictions of the tensor powers to the diagonal of the
product scaling surface; their frequencies are the sums of `n` zeros (`TheKunnethSquareCarriesTheSumsOfZeros`).

* **Schur** (`isPosDefKernel_mul`, `isPosDefKernel_pow`): products and powers of positive-definite
  kernels on a group are positive definite, through the Künneth inertia law and the diagonal.
* **Every Hadamard power of `K_ζ` is RH** (`riemannHypothesis_iff_isPosDefKernel_zetaKernel_pow`):
  for `n ≥ 1`, `K_ζ^n` is positive definite iff RH. If `K_ζ^n` is positive definite then
  `‖K_ζ(u)‖^n ≤ ‖K_ζ(1)‖^n`, so `K_ζ` is bounded, which is RH
  (`riemannHypothesis_of_norm_zetaKernel_le`).
* **The Künneth square dominates the index** (`negIndex_zetaKernel_le_negIndex_kunnethZeta`):
  `κ(K_ζ) ≤ κ(K_ζ ⊠ K_ζ)`; unless RH holds, `K_ζ` has a positive square, which multiplies every
  negative square of `K_ζ` into one of the square.
* **A finite Künneth index is Lindelöf-deep** (`lindelof_of_negIndex_kunnethZeta_lt_top`,
  `quasiRH_of_negIndex_kunnethZeta_lt_top`): a finite index for the Künneth square gives finitely many
  off-line zeros, hence Lindelöf and a zero-free half-plane.

The weight route over `𝔽_q` amplifies a fixed loss through tensor powers. For Weil's kernel no
tensor or Hadamard degree is easier than degree one: every degree carries RH, and every finite-index
statement at degree two already carries the finite stratum.
-/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

variable {G : Type*} [Group G]

/-- **Schur product for kernels on a group.** -/
theorem isPosDefKernel_mul {k l : G → ℂ} (hk : IsPosDefKernel k) (hl : IsPosDefKernel l) :
    IsPosDefKernel fun g => k g * l g := by
  have hherm : IsHermKernel fun g => k g * l g := fun g => by
    simp only [hk.1 g, hl.1 g, map_mul]
  refine (isPosDefKernel_iff hherm).mpr ?_
  have h := negIndex_mul_le_negIndex_tensorKernel k l
  rw [negIndex_tensorKernel_eq_zero hk hl] at h
  exact nonpos_iff_eq_zero.mp h

/-- **Hadamard powers of positive-definite kernels are positive definite.** -/
theorem isPosDefKernel_pow {k : G → ℂ} (hk : IsPosDefKernel k) (n : ℕ) :
    IsPosDefKernel fun g => k g ^ (n + 1) := by
  induction n with
  | zero => simpa using hk
  | succ n ih => simpa [pow_succ] using isPosDefKernel_mul ih hk

/-- **Every Hadamard power of Weil's kernel is RH.** -/
theorem riemannHypothesis_iff_isPosDefKernel_zetaKernel_pow (n : ℕ) :
    RiemannHypothesis ↔ IsPosDefKernel fun u => zetaKernel u ^ (n + 1) := by
  constructor
  · intro h
    exact isPosDefKernel_pow ((isPosDefKernel_iff isHermKernel_zetaKernel).mpr
      (riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp h)) n
  · intro h
    refine riemannHypothesis_of_norm_zetaKernel_le (C := ‖zetaKernel 1‖) fun u => ?_
    have hu := h.norm_le u
    have h1 : (zetaKernel 1 ^ (n + 1)).re ≤ ‖zetaKernel 1‖ ^ (n + 1) :=
      (Complex.re_le_norm _).trans (norm_pow _ _).le
    rw [norm_pow] at hu
    exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero n) (norm_nonneg _) (hu.trans h1)

/-- The `n`-th Hadamard power of `K_ζ` has no negative square iff RH. -/
theorem riemannHypothesis_iff_negIndex_zetaKernel_pow_eq_zero (n : ℕ) :
    RiemannHypothesis ↔ negIndex (fun u => zetaKernel u ^ (n + 1)) = 0 := by
  have hherm : IsHermKernel fun u => zetaKernel u ^ (n + 1) := fun u => by
    simp only [isHermKernel_zetaKernel u, map_pow]
  rw [riemannHypothesis_iff_isPosDefKernel_zetaKernel_pow n, isPosDefKernel_iff hherm]

/-- **The Künneth square dominates the index of Weil's kernel.** -/
theorem negIndex_zetaKernel_le_negIndex_kunnethZeta :
    negIndex zetaKernel ≤ negIndex kunnethZeta := by
  by_cases hRH : RiemannHypothesis
  · rw [riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH]; exact bot_le
  · have hpos : posIndex zetaKernel ≠ 0 := fun h0 =>
      hRH (riemannHypothesis_of_posIndex_zetaKernel_eq_zero h0)
    obtain ⟨m, x, hx⟩ := exists_hermNegIndex_pos (k := fun u => -zetaKernel u) hpos
    rw [gram_neg, hermNegIndex, neg_neg] at hx
    refine negIndex_le_iff.mpr fun n y => ?_
    refine le_trans ?_ (hermIndex_kronecker_le_negIndex_tensor isHermKernel_zetaKernel
      isHermKernel_zetaKernel x y)
    exact_mod_cast le_add_right (Nat.le_mul_of_pos_left _ hx)

/-- **A finite Künneth index forces Lindelöf.** -/
theorem lindelof_of_negIndex_kunnethZeta_lt_top (h : negIndex kunnethZeta < ⊤) :
    _root_.RHTower.LindelofSparse.LindelofCriticalLine :=
  lindelof_of_negIndex_zetaKernel_lt_top (negIndex_zetaKernel_le_negIndex_kunnethZeta.trans_lt h)

/-- **A finite Künneth index forces a zero-free half-plane.** -/
theorem quasiRH_of_negIndex_kunnethZeta_lt_top (h : negIndex kunnethZeta < ⊤) :
    ∃ α : ℝ, α < 1 / 2 ∧ _root_.RHTower.XiZeroHalfPlaneBound α :=
  quasiRH_of_negIndex_zetaKernel_lt_top (negIndex_zetaKernel_le_negIndex_kunnethZeta.trans_lt h)

end GaloisForLFunctions.RenormalizedIntersectionTheory
