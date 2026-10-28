import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeBecomesVisibleAtTheCriticalExponent

/-!
# The complete source is a dyadic multiresolution

The complete logarithmic cells `C_a = 1_{[log a, log(a+1))}` carry every mixed entry of Weil's form
(ArithmeticCastelnuovoSeveri). Two adjacent cells `C_{2a}`, `C_{2a+1}` fill `[log 2a, log(2a+2))`,
which is `C_a` translated by `log 2`. So the complete source is a copy of itself one dyadic level up.

* **The doubled cell** (`logCell_two_mul_add`): `C_{2a} + C_{2a+1} = T_{log 2} C_a`.
* **One renormalization step** (`sum_logCell_rg_step`): every complete step profile on cells
  `1, …, 2X + 1` is `c₁C₁`, plus the translate by `log 2` of the coarse profile with pair averages on
  cells `1, …, X`, plus the details `C_{2a} − C_{2a+1}` weighted by half the pair differences.
* **The multiresolution** (`sum_logCell_multiresolution`): on cells `1, …, 2^L − 1` the profile is
  a sum over levels `j < L` of the translates by `j log 2` of one generator cell `C₁` and of the
  level-`j` details, with coefficients the iterated averages and differences.
* **Level-Toeplitz law** (`orbitPairing_translate_translate`, `weilOrbitPairing_level`): for every
  translation-invariant functional, in particular every twisted Weil form `Q_λ`, the polarized
  pairing of level-`j` and level-`k` translates depends only on `k − j`. Diagonal blocks repeat at
  every level, and every reserve proved at one level holds at all levels (`weilQuadTw_level`).

Positivity of the complete form is therefore positivity on the `T_{log 2}`-orbits of finitely many
generators plus a payment of the couplings between levels; `ALevelIsPaidByItsReserve` is the calculus
of that payment.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis

/-- The complete logarithmic cell `C_a = 1_{[log a, log(a + 1))}`. -/
def logCell (a : ℕ) : ℝ → ℝ := Set.indicator (Set.Ico (Real.log a) (Real.log ((a : ℝ) + 1))) 1

/-- Translation `T_t f = f(· − t)`. -/
def translate (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun u => f (u - t)

theorem translate_add (t : ℝ) (f g : ℝ → ℝ) :
    translate t (f + g) = translate t f + translate t g := rfl

theorem translate_sub (t : ℝ) (f g : ℝ → ℝ) :
    translate t (f - g) = translate t f - translate t g := rfl

theorem translate_smul (t r : ℝ) (f : ℝ → ℝ) : translate t (r • f) = r • translate t f := rfl

theorem translate_sum {ι : Type*} (t : ℝ) (s : Finset ι) (g : ι → ℝ → ℝ) :
    translate t (∑ i ∈ s, g i) = ∑ i ∈ s, translate t (g i) := by
  funext u
  simp only [translate, Finset.sum_apply]

theorem translate_translate (s t : ℝ) (f : ℝ → ℝ) :
    translate s (translate t f) = translate (s + t) f := by
  funext u
  simp only [translate]
  ring_nf

theorem translate_zero (f : ℝ → ℝ) : translate 0 f = f := by
  funext u
  simp [translate]

/-- **The doubled cell is the translated cell**: `C_{2a} + C_{2a+1} = T_{log 2} C_a`. -/
theorem logCell_two_mul_add {a : ℕ} (ha : 1 ≤ a) :
    logCell (2 * a) + logCell (2 * a + 1) = translate (Real.log 2) (logCell a) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have c1 : ((2 * a : ℕ) : ℝ) + 1 = ((2 * a + 1 : ℕ) : ℝ) := by push_cast; ring
  have e0 : Real.log ((2 * a : ℕ) : ℝ) = Real.log 2 + Real.log a := by
    push_cast
    exact Real.log_mul two_ne_zero ha0.ne'
  have e2 : Real.log (((2 * a + 1 : ℕ) : ℝ) + 1) = Real.log 2 + Real.log ((a : ℝ) + 1) := by
    push_cast
    rw [show (2 * (a : ℝ) + 1 + 1) = 2 * ((a : ℝ) + 1) by ring]
    exact Real.log_mul two_ne_zero (by positivity)
  have m1 : Real.log ((2 * a : ℕ) : ℝ) ≤ Real.log ((2 * a + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have m2 : Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ Real.log (((2 * a + 1 : ℕ) : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hU := Set.Ico_union_Ico_eq_Ico m1 m2
  funext u
  calc (logCell (2 * a) + logCell (2 * a + 1)) u
      = (Set.Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ)) ∪
          Set.Ico (Real.log ((2 * a + 1 : ℕ) : ℝ)) (Real.log (((2 * a + 1 : ℕ) : ℝ) + 1))).indicator
          1 u := by
        rw [Set.indicator_union_of_disjoint Set.Ico_disjoint_Ico_same, Pi.add_apply]
        simp only [logCell, c1]
    _ = translate (Real.log 2) (logCell a) u := by
        rw [hU]
        simp only [translate, logCell, Set.indicator_apply, Set.mem_Ico, e0, e2]
        congr 1
        exact propext ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
          fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩

/-- The average coefficients of the next coarser level. -/
def coarseCoeff (c : ℕ → ℝ) (a : ℕ) : ℝ := (c (2 * a) + c (2 * a + 1)) / 2

/-- The detail coefficients of a level. -/
def detailCoeff (c : ℕ → ℝ) (a : ℕ) : ℝ := (c (2 * a) - c (2 * a + 1)) / 2

/-- The detail of the pair of cells `2a`, `2a + 1`. -/
def logDetail (a : ℕ) : ℝ → ℝ := logCell (2 * a) - logCell (2 * a + 1)

/-- A sum over `1, …, 2X + 1` is its first term plus the sums over the pairs `2a, 2a + 1`. -/
theorem sum_Icc_two_mul_add_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (X : ℕ) :
    ∑ a ∈ Icc 1 (2 * X + 1), f a = f 1 + ∑ a ∈ Icc 1 X, (f (2 * a) + f (2 * a + 1)) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [show 2 * (X + 1) + 1 = (2 * X + 1) + 1 + 1 by ring, sum_Icc_succ_top (by omega),
      sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega)]
    rw [show 2 * X + 1 + 1 = 2 * (X + 1) by ring, show 2 * (X + 1) + 1 = 2 * X + 1 + 1 + 1 by ring]
    abel

/-- **One renormalization step of the complete source.** -/
theorem sum_logCell_rg_step (c : ℕ → ℝ) (X : ℕ) :
    ∑ a ∈ Icc 1 (2 * X + 1), c a • logCell a =
      c 1 • logCell 1 + translate (Real.log 2) (∑ a ∈ Icc 1 X, coarseCoeff c a • logCell a) +
        ∑ a ∈ Icc 1 X, detailCoeff c a • logDetail a := by
  rw [sum_Icc_two_mul_add_one, translate_sum, add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun a ha => ?_
  rw [translate_smul, ← logCell_two_mul_add (mem_Icc.mp ha).1, coarseCoeff, detailCoeff, logDetail]
  funext u
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The level-`j` part of the multiresolution: the generator cell and the level-`j` details. -/
def levelPart (c : ℕ → ℝ) (L j : ℕ) : ℝ → ℝ :=
  (coarseCoeff^[j] c) 1 • logCell 1 +
    ∑ a ∈ Icc 1 (2 ^ (L - 1 - j) - 1), detailCoeff (coarseCoeff^[j] c) a • logDetail a

/-- **The dyadic multiresolution of the complete source**: on cells `1, …, 2^L − 1`,
`Σ c_a C_a = Σ_{j < L} T_{j log 2}(c^{(j)}_1 C₁ + Σ_a d^{(j)}_a (C_{2a} − C_{2a+1}))`, with
`c^{(j)}` the `j`-fold pair averages and `d^{(j)}` their half differences. -/
theorem sum_logCell_multiresolution (L : ℕ) (c : ℕ → ℝ) :
    ∑ a ∈ Icc 1 (2 ^ L - 1), c a • logCell a =
      ∑ j ∈ range L, translate (j * Real.log 2) (levelPart c L j) := by
  induction L generalizing c with
  | zero => simp
  | succ L ih =>
    have h2 : 2 ^ (L + 1) - 1 = 2 * (2 ^ L - 1) + 1 := by
      have := Nat.one_le_two_pow (n := L); rw [pow_succ]; omega
    rw [h2, sum_logCell_rg_step, ih (coarseCoeff c), translate_sum, sum_range_succ']
    simp only [translate_translate, Nat.cast_succ, Nat.cast_zero, zero_mul, translate_zero]
    have hlev0 : levelPart c (L + 1) 0 =
        c 1 • logCell 1 + ∑ a ∈ Icc 1 (2 ^ L - 1), detailCoeff c a • logDetail a := by
      rw [levelPart, Function.iterate_zero_apply, show L + 1 - 1 - 0 = L by omega]
    have hlev : ∀ x ∈ range L, translate (Real.log 2 + x * Real.log 2)
        (levelPart (coarseCoeff c) L x) = translate ((x + 1) * Real.log 2) (levelPart c (L + 1) (x + 1)) := by
      intro x _
      rw [show Real.log 2 + x * Real.log 2 = (x + 1) * Real.log 2 by ring, levelPart, levelPart,
        Function.iterate_succ_apply, show L + 1 - 1 - (x + 1) = L - 1 - x by omega]
    rw [hlev0, sum_congr rfl hlev]
    abel

/-! ### The level-Toeplitz law -/

/-- The polarized pairing `(Φ(f + g) − Φ(f − g))/4` of a functional `Φ`. -/
def orbitPairing (Φ : (ℝ → ℝ) → ℝ) (f g : ℝ → ℝ) : ℝ := (Φ (f + g) - Φ (f - g)) / 4

/-- A translation-invariant functional has a translation-invariant pairing. -/
theorem orbitPairing_translate {Φ : (ℝ → ℝ) → ℝ} (hΦ : ∀ t f, Φ (translate t f) = Φ f) (t : ℝ)
    (f g : ℝ → ℝ) : orbitPairing Φ (translate t f) (translate t g) = orbitPairing Φ f g := by
  rw [orbitPairing, orbitPairing, ← translate_add, ← translate_sub, hΦ, hΦ]

/-- **The level-Toeplitz law**: the pairing of the level-`j` and level-`k` translates (`j ≤ k`)
equals the pairing of the level-`0` generator with the level-`(k − j)` translate. -/
theorem orbitPairing_translate_translate {Φ : (ℝ → ℝ) → ℝ}
    (hΦ : ∀ t f, Φ (translate t f) = Φ f) (ℓ : ℝ) {j k : ℕ} (hjk : j ≤ k) (f g : ℝ → ℝ) :
    orbitPairing Φ (translate (j * ℓ) f) (translate (k * ℓ) g) =
      orbitPairing Φ f (translate ((k - j : ℕ) * ℓ) g) := by
  have hk : translate (k * ℓ) g = translate (j * ℓ) (translate ((k - j : ℕ) * ℓ) g) := by
    rw [translate_translate, Nat.cast_sub hjk]
    ring_nf
  rw [hk, orbitPairing_translate hΦ]

/-- Every twisted Weil form is translation invariant. -/
theorem weilQuadTw_translate (lam : ℕ → ℝ) (t : ℝ) (f : ℝ → ℝ) :
    weilQuadTw lam (translate t f) = weilQuadTw lam f :=
  weilQuadTw_comp_sub lam f t

/-- **Every level repeats the generator energies**: `Q_λ(T_{j log 2} h) = Q_λ(h)`, so a reserve
proved for a block at one level holds for its translates at all levels. -/
theorem weilQuadTw_level (lam : ℕ → ℝ) (j : ℕ) (h : ℝ → ℝ) :
    weilQuadTw lam (translate (j * Real.log 2) h) = weilQuadTw lam h :=
  weilQuadTw_translate lam _ h

/-- **The level-Toeplitz law for Weil's forms**: for every weight `λ`, the pairing of level-`j` and
level-`k` translates of the generators depends only on `k − j`. -/
theorem weilOrbitPairing_level (lam : ℕ → ℝ) {j k : ℕ} (hjk : j ≤ k) (f g : ℝ → ℝ) :
    orbitPairing (weilQuadTw lam) (translate (j * Real.log 2) f) (translate (k * Real.log 2) g) =
      orbitPairing (weilQuadTw lam) f (translate ((k - j : ℕ) * Real.log 2) g) :=
  orbitPairing_translate_translate (weilQuadTw_translate lam) _ hjk f g

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
