import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePairingOfTheDegreePointsWeighsTheZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheEnergyOfAWindowIsTheJumpFormOfItsFlatPacket

/-!
# Weil's form on step packets is determined by its values on windows

For a packet `g` with autocorrelation `h_g` put

`𝔚_Q(g) = 2 d₁ d₂ + A(0) h_g(0) + ∫_0^∞ 2ω(x)(h_g(0) − h_g(x)) dx
  − 2 Σ_{2 ≤ k ≤ Q} Λ(k) k^{−1/2} h_g(log k)`   (`packetForm`),

with the degrees `d₁ = ∫ g e^{−u/2}`, `d₂ = ∫ g e^{u/2}`, the Lévy density `ω` and the constant
`A(0)` of Weil's archimedean form. The expression needs no smoothness of `g`.

* For `g ∈ C²_c` it is the sum over the zeros `Z(g)` (`zeroSum_eq_packetForm`).
* **Polar expansion** (`PolarOn`, `polarOn_packetForm`). Every term of `𝔚_Q` is the diagonal of
  a bilinear expression, so on the combinations of a finite family `v_j`
  `q(Σ τ_j v_j) = ½ Σ_{j,l} τ_j τ_l (q(v_j) + q(v_l) − q(v_l − v_j))`.
* **Nested flat packets** (`polarOn_packetForm_flatPacket`,
  `packetForm_flatPacket_sub_flatPacket`). For `v_j = e^{u/2}` on `(log x₀, log x_j]` the
  differences are flat packets of windows again, up to sign. So `𝔚_Q` of a step packet is a
  quadratic form whose entries are values of `𝔚_Q` on single windows.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The form of a packet -/

/-- Weil's form of a packet through its autocorrelation: pole term, archimedean constant,
jump integral, and the contacts up to `Q`. -/
def packetForm (Q : ℕ) (g : ℝ → ℝ) : ℝ :=
  2 * ((∫ u, g u * Real.exp (-u / 2)) * ∫ u, g u * Real.exp (u / 2)) +
    (EF.gammaBracket 0 * packetAutocorr g 0 + ∫ x in Set.Ioi 0, levyJump g x) -
    2 * ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr g (Real.log k)

theorem exists_natCast_le_abs_imp_eq_zero {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ R : ℕ, ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0 := by
  obtain ⟨A, hA⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨⌈A⌉₊ + 1, fun u hu => ?_⟩
  by_contra hne
  have h := hA (subset_tsupport _ hne)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  have h1 : A ≤ ⌈A⌉₊ := Nat.le_ceil A
  push_cast at hu
  linarith

/-- **On a packet of class `C²` the form is the sum over the zeros.** -/
theorem zeroSum_eq_packetForm {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {Q : ℕ} (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) :
    zeroSum f = packetForm Q f := by
  obtain ⟨R, hsupp⟩ := exists_natCast_le_abs_imp_eq_zero hfc
  have hcont := hf.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hfc
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by norm_num)
  have hB' : ∀ u, |f u| ≤ B := fun u => by
    rw [← Real.norm_eq_abs]
    exact hB u
  have hL : ∀ u v, |f u - f v| ≤ (C : ℝ) * |u - v| := fun u v => by
    have h := hC.dist_le_mul u v
    rwa [Real.dist_eq, Real.dist_eq] at h
  have hweil : _root_.RHTower.WeilOneSided.weilArchRe
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
      (_root_.RHTower.weilPoleTerm
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x :=
    weilArchRe_sub_pole_packet hf hfc hsupp hB' hL
  have hpole := weilPoleTerm_packet hcont hfc
  rw [zeroSum_eq_weilFullFunctional hf hfc, re_weilFullFunctional_packet f hQ, packetForm]
  linarith

/-! ### The polar identity of a quadratic functional -/

section Polar

variable {α ι : Type*}

/-- The polar identity of a functional `q` on the combinations of a finite family `v`:
`q(Σ τ_j v_j) = ½ Σ_{j,l} τ_j τ_l (q(v_j) + q(v_l) − q(v_l − v_j))`. It holds when `q` is the
diagonal of a bilinear expression on the family. -/
def PolarOn (q : (α → ℝ) → ℝ) (v : ι → α → ℝ) (s : Finset ι) : Prop :=
  ∀ τ : ι → ℝ, q (fun u => ∑ j ∈ s, τ j * v j u) =
    1 / 2 * ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * (q (v j) + q (v l) - q (fun u => v l u - v j u))

variable {q q₁ q₂ : (α → ℝ) → ℝ} {v : ι → α → ℝ} {s : Finset ι}

/-- The diagonal of a bilinear expression `b` on the family satisfies the polar identity. -/
theorem polarOn_of_bilin (b : ι → ι → ℝ)
    (h1 : ∀ τ : ι → ℝ, q (fun u => ∑ j ∈ s, τ j * v j u) = ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * b j l)
    (h2 : ∀ j ∈ s, ∀ l ∈ s, q (fun u => v l u - v j u) = b l l - b l j - b j l + b j j)
    (h3 : ∀ j ∈ s, q (v j) = b j j) : PolarOn q v s := by
  intro τ
  rw [h1 τ]
  have e : ∀ j ∈ s, ∀ l ∈ s,
      τ j * τ l * (q (v j) + q (v l) - q (fun u => v l u - v j u)) =
        τ j * τ l * b j l + τ l * τ j * b l j := fun j hj l hl => by
    rw [h2 j hj l hl, h3 j hj, h3 l hl]
    ring
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => e j hj l hl]
  have hc : ∑ j ∈ s, ∑ l ∈ s, τ l * τ j * b l j = ∑ j ∈ s, ∑ l ∈ s, τ j * τ l * b j l :=
    Finset.sum_comm
  simp only [Finset.sum_add_distrib]
  rw [hc]
  ring

theorem PolarOn.add (h₁ : PolarOn q₁ v s) (h₂ : PolarOn q₂ v s) :
    PolarOn (fun g => q₁ g + q₂ g) v s := by
  intro τ
  beta_reduce
  rw [h₁ τ, h₂ τ, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem PolarOn.sub (h₁ : PolarOn q₁ v s) (h₂ : PolarOn q₂ v s) :
    PolarOn (fun g => q₁ g - q₂ g) v s := by
  intro τ
  beta_reduce
  rw [h₁ τ, h₂ τ, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem PolarOn.const_mul (c : ℝ) (h : PolarOn q v s) : PolarOn (fun g => c * q g) v s := by
  intro τ
  beta_reduce
  rw [h τ, mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem PolarOn.sum {κ : Type*} (t : Finset κ) {Q : κ → (α → ℝ) → ℝ}
    (h : ∀ k ∈ t, PolarOn (Q k) v s) : PolarOn (fun g => ∑ k ∈ t, Q k g) v s := by
  intro τ
  beta_reduce
  rw [Finset.sum_congr rfl fun k hk => h k hk τ, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The polar identity passes under an integral, when the terms on single members and on
differences are integrable. -/
theorem PolarOn.setIntegral {F : (α → ℝ) → ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (h : ∀ x ∈ S, PolarOn (fun g => F g x) v s)
    (hv : ∀ j ∈ s, IntegrableOn (F (v j)) S)
    (hd : ∀ j ∈ s, ∀ l ∈ s, IntegrableOn (F (fun u => v l u - v j u)) S) :
    PolarOn (fun g => ∫ x in S, F g x) v s := by
  intro τ
  beta_reduce
  have hint : ∀ j ∈ s, ∀ l ∈ s, Integrable (fun x => τ j * τ l *
      (F (v j) x + F (v l) x - F (fun u => v l u - v j u) x)) (volume.restrict S) :=
    fun j hj l hl => (((hv j hj).add (hv l hl)).sub (hd j hj l hl)).const_mul _
  rw [setIntegral_congr_fun hS (fun x hx => h x hx τ), integral_const_mul,
    integral_finsetSum _ fun j hj => integrable_finsetSum _ fun l hl => hint j hj l hl]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun l hl => hint j hj l hl]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hjl : Integrable (fun x => F (v j) x + F (v l) x) (volume.restrict S) :=
    (hv j hj).add (hv l hl)
  rw [integral_const_mul]
  congr 1
  exact (integral_sub hjl (hd j hj l hl)).trans
    (congrArg (· - _) (integral_add (hv j hj) (hv l hl)))

end Polar

/-! ### The form of a packet satisfies the polar identity -/

section PacketPolar

variable {ι : Type*} {v : ι → ℝ → ℝ} {s : Finset ι}

theorem integral_sum_mul (τ : ι → ℝ) (w : ℝ → ℝ)
    (h : ∀ j ∈ s, Integrable (fun u => v j u * w u)) :
    ∫ u, (∑ j ∈ s, τ j * v j u) * w u = ∑ j ∈ s, τ j * ∫ u, v j u * w u := by
  have e : (fun u => (∑ j ∈ s, τ j * v j u) * w u) =
      fun u => ∑ j ∈ s, τ j * (v j u * w u) := by
    funext u
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ fun j hj => (h j hj).const_mul (τ j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem integral_mul_sum (τ : ι → ℝ) (w : ℝ → ℝ) (y : ι → ℝ → ℝ)
    (h : ∀ j ∈ s, Integrable (fun u => w u * y j u)) :
    ∫ u, w u * ∑ j ∈ s, τ j * y j u = ∑ j ∈ s, τ j * ∫ u, w u * y j u := by
  have e : (fun u => w u * ∑ j ∈ s, τ j * y j u) =
      fun u => ∑ j ∈ s, τ j * (w u * y j u) := by
    funext u
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ fun j hj => (h j hj).const_mul (τ j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- The product of the two degrees. -/
theorem polarOn_degrees
    (hm : ∀ j ∈ s, Integrable (fun u => v j u * Real.exp (-u / 2)))
    (hp : ∀ j ∈ s, Integrable (fun u => v j u * Real.exp (u / 2))) :
    PolarOn (fun g : ℝ → ℝ => (∫ u, g u * Real.exp (-u / 2)) * ∫ u, g u * Real.exp (u / 2))
      v s := by
  refine polarOn_of_bilin
    (fun j l => (∫ u, v j u * Real.exp (-u / 2)) * ∫ u, v l u * Real.exp (u / 2)) ?_ ?_
    (fun _ _ => rfl)
  · intro τ
    beta_reduce
    rw [integral_sum_mul τ _ hm, integral_sum_mul τ _ hp, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  · intro j hj l hl
    beta_reduce
    have e1 : (∫ u, (v l u - v j u) * Real.exp (-u / 2)) =
        (∫ u, v l u * Real.exp (-u / 2)) - ∫ u, v j u * Real.exp (-u / 2) := by
      rw [← integral_sub (hm l hl) (hm j hj)]
      exact integral_congr_ae (Eventually.of_forall fun u => by ring)
    have e2 : (∫ u, (v l u - v j u) * Real.exp (u / 2)) =
        (∫ u, v l u * Real.exp (u / 2)) - ∫ u, v j u * Real.exp (u / 2) := by
      rw [← integral_sub (hp l hl) (hp j hj)]
      exact integral_congr_ae (Eventually.of_forall fun u => by ring)
    rw [e1, e2]
    ring

/-- The autocorrelation at a displacement. -/
theorem polarOn_packetAutocorr
    (hc : ∀ j ∈ s, ∀ l ∈ s, ∀ x : ℝ, Integrable (fun u => v j u * v l (u + x))) (x : ℝ) :
    PolarOn (fun g : ℝ → ℝ => packetAutocorr g x) v s := by
  refine polarOn_of_bilin (fun j l => ∫ u, v j u * v l (u + x)) ?_ ?_ (fun _ _ => rfl)
  · intro τ
    simp only [packetAutocorr]
    have hw : ∀ j ∈ s, Integrable (fun u => v j u * ∑ l ∈ s, τ l * v l (u + x)) :=
      fun j hj => by
        have e : (fun u => v j u * ∑ l ∈ s, τ l * v l (u + x)) =
            fun u => ∑ l ∈ s, τ l * (v j u * v l (u + x)) := by
          funext u
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [e]
        exact integrable_finsetSum _ fun l hl => (hc j hj l hl x).const_mul (τ l)
    rw [integral_sum_mul τ _ hw]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_mul_sum τ _ (fun l u => v l (u + x)) fun l hl => hc j hj l hl x,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  · intro j hj l hl
    simp only [packetAutocorr]
    have e : (fun u => (v l u - v j u) * (v l (u + x) - v j (u + x))) =
        fun u => v l u * v l (u + x) - v l u * v j (u + x) - v j u * v l (u + x) +
          v j u * v j (u + x) := by
      funext u
      ring
    have i1 := hc l hl l hl x
    have i2 := hc l hl j hj x
    have i3 := hc j hj l hl x
    have i4 := hc j hj j hj x
    have i12 : Integrable fun u => v l u * v l (u + x) - v l u * v j (u + x) := i1.sub i2
    have i123 : Integrable fun u =>
        v l u * v l (u + x) - v l u * v j (u + x) - v j u * v l (u + x) := i12.sub i3
    rw [e]
    exact (integral_add i123 i4).trans (by rw [integral_sub i12 i3, integral_sub i1 i2])

/-- **The form of a packet satisfies the polar identity** on a family whose members and whose
differences have integrable jump integrands. -/
theorem polarOn_packetForm (Q : ℕ)
    (hm : ∀ j ∈ s, Integrable (fun u => v j u * Real.exp (-u / 2)))
    (hp : ∀ j ∈ s, Integrable (fun u => v j u * Real.exp (u / 2)))
    (hc : ∀ j ∈ s, ∀ l ∈ s, ∀ x : ℝ, Integrable (fun u => v j u * v l (u + x)))
    (hJ : ∀ j ∈ s, IntegrableOn (levyJump (v j)) (Set.Ioi 0))
    (hJd : ∀ j ∈ s, ∀ l ∈ s, IntegrableOn (levyJump (fun u => v l u - v j u)) (Set.Ioi 0)) :
    PolarOn (packetForm Q) v s := by
  have hA := polarOn_packetAutocorr hc
  have hjump : PolarOn (fun g : ℝ → ℝ => ∫ x in Set.Ioi 0, levyJump g x) v s :=
    PolarOn.setIntegral measurableSet_Ioi
      (fun x _ => ((hA 0).sub (hA x)).const_mul (2 * _root_.RHTower.archLevyDensity x)) hJ hJd
  have hsum : PolarOn (fun g : ℝ → ℝ =>
      ∑ k ∈ Icc 2 Q, contactWeight k * packetAutocorr g (Real.log k)) v s :=
    PolarOn.sum _ fun k _ => (hA (Real.log k)).const_mul (contactWeight k)
  exact (((polarOn_degrees hm hp).const_mul 2).add
    (((hA 0).const_mul (EF.gammaBracket 0)).add hjump)).sub (hsum.const_mul 2)

end PacketPolar

/-! ### Flat packets -/

section Flat

variable {a b c : ℝ}

theorem measurable_flatPacket (a b : ℝ) : Measurable (flatPacket a b) :=
  ((Real.continuous_exp.comp (continuous_id.div_const 2)).measurable).indicator measurableSet_Ioc

theorem abs_flatPacket_le (a b u : ℝ) : |flatPacket a b u| ≤ Real.exp (Real.log b / 2) := by
  simp only [flatPacket, Set.indicator_apply, Set.mem_Ioc]
  split_ifs with h
  · rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [h.2])
  · rw [abs_zero]
    exact (Real.exp_pos _).le

theorem flatPacket_mul (a b : ℝ) (w : ℝ → ℝ) :
    (fun u => flatPacket a b u * w u) =
      Set.indicator (Set.Ioc (Real.log a) (Real.log b)) fun u => Real.exp (u / 2) * w u := by
  funext u
  exact (Set.indicator_mul_left _ _ _).symm

theorem integrable_flatPacket_mul (a b : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Integrable fun u => flatPacket a b u * w u := by
  rw [flatPacket_mul]
  exact ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hw).integrableOn_Ioc
    |>.integrable_indicator measurableSet_Ioc

theorem integrable_flatPacket (a b : ℝ) : Integrable (flatPacket a b) := by
  have h := integrable_flatPacket_mul a b (w := fun _ => (1 : ℝ)) continuous_const
  simpa using h

/-- Products of translated flat packets are integrable. -/
theorem integrable_flatPacket_mul_flatPacket (a b c d x : ℝ) :
    Integrable fun u => flatPacket a b u * flatPacket c d (u + x) := by
  have hmeas : Measurable fun u => flatPacket a b u * flatPacket c d (u + x) :=
    (measurable_flatPacket a b).mul ((measurable_flatPacket c d).comp (measurable_id.add_const x))
  refine ((integrable_flatPacket a b).norm.mul_const (Real.exp (Real.log d / 2))).mono'
    hmeas.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (abs_flatPacket_le c d _) (norm_nonneg _)

/-- The first degree of a flat packet: the logarithmic length of its window. -/
theorem integral_flatPacket_mul_exp_neg (ha : 0 < a) (hab : a ≤ b) :
    ∫ u, flatPacket a b u * Real.exp (-u / 2) = Real.log b - Real.log a := by
  have hle : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have e : (fun u : ℝ => Real.exp (u / 2) * Real.exp (-u / 2)) = fun _ => (1 : ℝ) := by
    funext u
    rw [← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
  rw [flatPacket_mul, integral_indicator measurableSet_Ioc, e,
    ← intervalIntegral.integral_of_le hle, integral_one]

/-- The second degree of a flat packet: the length of its window. -/
theorem integral_flatPacket_mul_exp (ha : 0 < a) (hab : a ≤ b) :
    ∫ u, flatPacket a b u * Real.exp (u / 2) = b - a := by
  have hle : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have e : (fun u : ℝ => Real.exp (u / 2) * Real.exp (u / 2)) = fun u => Real.exp u := by
    funext u
    rw [← Real.exp_add, add_halves]
  rw [flatPacket_mul, integral_indicator measurableSet_Ioc, e,
    ← intervalIntegral.integral_of_le hle, integral_exp, Real.exp_log (ha.trans_le hab),
    Real.exp_log ha]

/-- Nested flat packets differ by the flat packet of the window between their ends. -/
theorem flatPacket_sub_flatPacket (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (u : ℝ) :
    flatPacket a c u - flatPacket a b u = flatPacket b c u := by
  have h1 : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have h2 : Real.log b ≤ Real.log c := Real.log_le_log (ha.trans_le hab) hbc
  simp only [flatPacket, Set.indicator_apply, Set.mem_Ioc]
  by_cases hub : u ≤ Real.log b
  · have huc : u ≤ Real.log c := hub.trans h2
    rw [if_neg (fun h : Real.log b < u ∧ u ≤ Real.log c => absurd h.1 (not_lt.mpr hub))]
    by_cases hua : Real.log a < u
    · rw [if_pos ⟨hua, huc⟩, if_pos ⟨hua, hub⟩, sub_self]
    · rw [if_neg (fun h : Real.log a < u ∧ u ≤ Real.log c => hua h.1),
        if_neg (fun h : Real.log a < u ∧ u ≤ Real.log b => hua h.1), sub_zero]
  · have hbu : Real.log b < u := lt_of_not_ge hub
    have hau : Real.log a < u := lt_of_le_of_lt h1 hbu
    rw [if_neg (fun h : Real.log a < u ∧ u ≤ Real.log b => hub h.2)]
    by_cases huc : u ≤ Real.log c
    · rw [if_pos ⟨hau, huc⟩, if_pos ⟨hbu, huc⟩, sub_zero]
    · rw [if_neg (fun h : Real.log a < u ∧ u ≤ Real.log c => huc h.2),
        if_neg (fun h : Real.log b < u ∧ u ≤ Real.log c => huc h.2), sub_zero]

theorem packetAutocorr_neg_fun (g : ℝ → ℝ) (x : ℝ) :
    packetAutocorr (fun u => -g u) x = packetAutocorr g x := by
  simp only [packetAutocorr, neg_mul_neg]

theorem levyJump_neg_fun (g : ℝ → ℝ) : levyJump (fun u => -g u) = levyJump g := by
  funext x
  simp only [levyJump, packetAutocorr_neg_fun]

/-- The form does not see the sign of a packet. -/
theorem packetForm_neg_fun (Q : ℕ) (g : ℝ → ℝ) : packetForm Q (fun u => -g u) = packetForm Q g := by
  have e1 : (∫ u, -g u * Real.exp (-u / 2)) = -∫ u, g u * Real.exp (-u / 2) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  have e2 : (∫ u, -g u * Real.exp (u / 2)) = -∫ u, g u * Real.exp (u / 2) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  simp only [packetForm, levyJump_neg_fun, packetAutocorr_neg_fun, e1, e2, neg_mul_neg]

/-- The jump integrand of a flat packet is integrable. -/
theorem integrableOn_levyJump_flatPacket (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (levyJump (flatPacket a b)) (Set.Ioi 0) := by
  rcases hab.eq_or_lt with rfl | hlt
  · refine (integrableOn_zero (s := Set.Ioi (0 : ℝ))).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    rw [levyJump, packetAutocorr_flatPacket_of_ge le_rfl (by rw [sub_self]),
      packetAutocorr_flatPacket_of_ge hx0 (by rw [sub_self]; exact hx0), sub_self, mul_zero]
  · have hc : 0 < Real.log b - Real.log a := sub_pos.mpr (Real.log_lt_log ha hlt)
    have hcontR : Continuous fun x => 2 * b * flatRateOut x + 2 * a * flatRateIn x :=
      (continuous_const.mul continuous_flatRateOut).add
        (continuous_const.mul continuous_flatRateIn)
    have hI1 : IntegrableOn (levyJump (flatPacket a b))
        (Set.Ioc 0 (Real.log b - Real.log a)) :=
      (hcontR.integrableOn_Ioc).congr_fun
        (fun x hx => (levyJump_flatPacket_of_le ha hlt.le hx.1 hx.2).symm) measurableSet_Ioc
    have hI0 : IntegrableOn (fun x => 2 * (b - a) * _root_.RHTower.archLevyDensity x)
        (Set.Ioi (Real.log b - Real.log a)) :=
      Integrable.const_mul
        (_root_.RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hc) _
    have hI2 : IntegrableOn (levyJump (flatPacket a b)) (Set.Ioi (Real.log b - Real.log a)) :=
      hI0.congr_fun (fun x hx =>
        (levyJump_flatPacket_of_ge ha hlt.le (hc.le.trans (le_of_lt hx)) (le_of_lt hx)).symm)
        measurableSet_Ioi
    rw [← Set.Ioc_union_Ioi_eq_Ioi hc.le]
    exact hI1.union hI2

end Flat

/-! ### Nested flat packets -/

section Nested

variable {ι : Type*} {s : Finset ι} {x : ι → ℝ} {x₀ : ℝ}

/-- The difference of two nested flat packets is, up to sign, the flat packet of the window
between their ends. -/
theorem flatPacket_sub_eq (hx₀ : 0 < x₀) {y z : ℝ} (hy : x₀ ≤ y) (hz : x₀ ≤ z) :
    (fun u => flatPacket x₀ z u - flatPacket x₀ y u) = flatPacket (min y z) (max y z) ∨
      (fun u => flatPacket x₀ z u - flatPacket x₀ y u) =
        fun u => -flatPacket (min y z) (max y z) u := by
  rcases le_total y z with h | h
  · left
    funext u
    rw [min_eq_left h, max_eq_right h, flatPacket_sub_flatPacket hx₀ hy h]
  · right
    funext u
    rw [min_eq_right h, max_eq_left h, ← flatPacket_sub_flatPacket hx₀ hz h u, neg_sub]

/-- **The form on a difference of nested flat packets is the form on the window between their
ends.** -/
theorem packetForm_flatPacket_sub_flatPacket (Q : ℕ) (hx₀ : 0 < x₀) {y z : ℝ} (hy : x₀ ≤ y)
    (hz : x₀ ≤ z) :
    packetForm Q (fun u => flatPacket x₀ z u - flatPacket x₀ y u) =
      packetForm Q (flatPacket (min y z) (max y z)) := by
  rcases flatPacket_sub_eq hx₀ hy hz with h | h
  · rw [h]
  · rw [h, packetForm_neg_fun]

/-- **The form of a packet satisfies the polar identity on nested flat packets.** -/
theorem polarOn_packetForm_flatPacket (Q : ℕ) (hx₀ : 0 < x₀) (hx : ∀ j ∈ s, x₀ ≤ x j) :
    PolarOn (packetForm Q) (fun j => flatPacket x₀ (x j)) s := by
  refine polarOn_packetForm Q
    (fun j _ => integrable_flatPacket_mul _ _ (by fun_prop))
    (fun j _ => integrable_flatPacket_mul _ _ (by fun_prop))
    (fun j _ l _ y => integrable_flatPacket_mul_flatPacket _ _ _ _ _)
    (fun j hj => integrableOn_levyJump_flatPacket hx₀ (hx j hj))
    (fun j hj l hl => ?_)
  have hpos : 0 < min (x j) (x l) := lt_min (hx₀.trans_le (hx j hj)) (hx₀.trans_le (hx l hl))
  have hI := integrableOn_levyJump_flatPacket hpos (min_le_max (a := x j) (b := x l))
  rcases flatPacket_sub_eq hx₀ (hx j hj) (hx l hl) with h | h
  · rw [h]
    exact hI
  · rw [h, levyJump_neg_fun]
    exact hI

end Nested

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
