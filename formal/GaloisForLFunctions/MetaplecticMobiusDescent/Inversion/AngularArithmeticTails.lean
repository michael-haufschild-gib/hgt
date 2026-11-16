import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularDyadicBlocks

/-!
# Uniform tails of angular reflected arithmetic sources

The exact angular coefficient has the original norm bound. Radial kernel decay therefore
controls raw and dyadic tails with unchanged conductor and scale costs. Finite source
seminorms yield one polynomial height order across all reflected arithmetic data.
-/

open MeasureTheory Set
open scoped BigOperators Classical ContDiff ComplexConjugate SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation
open CompletedDyadic CanonicalQuadraticSieve InverseMoment InverseKernelSourceUniform
namespace InverseReflectedArithmeticHeight
open InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O
universe u

theorem angular_literal_reflected_raw_tail_arithmetic_uniform (ℓ : ℕ) (a₀ b₀ : ℝ) (ha₀ : 0< a₀) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0< C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then lambda^2∣a-1 else lambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0< scale → 0< T →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤ scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
      Summable (fun x => ‖if cut x then angularRawDualKernelTerm ℓ V scale 1 completedRamifiedStep
        (angularLiteralRawCoefficient ℓ G D s hc j S u) x else 0‖) ∧
      ‖∑' x, if cut x then angularRawDualKernelTerm ℓ V scale 1 completedRamifiedStep
        (angularLiteralRawCoefficient ℓ G D s hc j S u) x else 0‖≤
      C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := angular_raw_kernel_tail ℓ a₀ b₀ completedRamifiedStep ha₀ completedRamifiedStep_gt_one A
  refine ⟨orders,C,hC,?_⟩
  intro N a c mode V hV ι _ G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  have hh := hb V hV scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T hs (by norm_num) (Nat.cast_nonneg _) hT
    (angularLiteralRawCoefficient ℓ G D s hc j S u) (angularLiteralRawCoefficient_norm ℓ G D s hc hN hbase hchar j hj S u) cut hcut
  simpa only [one_pow,mul_one] using hh

theorem angular_literal_reflected_dyadic_tail_arithmetic_uniform (ℓ : ℕ) (lo hi : ℝ) (hlo : 0< lo) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0< C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi →
    ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then lambda^2∣a-1 else lambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0< scale → 0< T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤ rawDyadicCenter scale i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          angularRawDualKernelTerm ℓ V scale 1 completedRamifiedStep
            (angularLiteralRawCoefficient ℓ G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0‖≤
        C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := angular_literal_reflected_raw_tail_arithmetic_uniform ℓ lo hi hlo A
  refine ⟨orders,C,hC,?_⟩
  intro N a c mode V hV ι _ G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  obtain ⟨hn,hh⟩ := hb (N:=N) (a:=a) (c:=c) (mode:=mode) V hV G D s hc hN hbase hchar j hj S u scale T hs hT
    (fun x => cut (rawDyadicLabel x)) (fun x hx => by
      have hc' := hcut (rawDyadicLabel x) hx
      have hl := rawDyadicCenter_lower scale hs.le x
      linarith)
  rw [tsum_cut_dyadic _ cut hn.of_norm] at hh
  exact hh

theorem angular_literal_dyadic_tail_height_arithmetic_uniform (ℓ : ℕ) (lo hi : ℝ) (hlo : 0< lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0< C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then lambda^2∣a-1 else lambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0< X → 0< T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤ rawDyadicCenter (literalRawScale G s X) i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        angularLiteralDyadicBlock ℓ G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨orders,C,hC,hbound⟩ := angular_literal_reflected_dyadic_tail_arithmetic_uniform ℓ lo hi hlo A
  let V := CompletedHeight.vstarSchwartz W lo hi hlo hWs hW
  have hV : Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi := Vstar_support W lo hi hWs
  obtain ⟨H,hH,hpoly⟩ := CompletedHeight.normTwistedSource_schwartz V lo hi hlo hV
  obtain ⟨degree,C₁,hC₁,hsemi⟩ := hpoly orders
  have hlink (θ : ℝ) : (H θ : ℝ→ℂ)=Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hH θ x]
    change kernelLogPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(kernelLogPhase θ (Real.log x)*W x)
    ring
  have hHs (θ : ℝ) : Function.support (H θ : ℝ→ℂ)⊆Set.Icc lo hi := by
    intro x hx
    change H θ x≠0 at hx
    rw [hH θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  refine ⟨degree,C*C₁,mul_pos hC hC₁,?_⟩
  intro N a c mode ι _ G D s hc hN hbase hchar j hj S u θ X T hX hT cut hcut
  have hh := hbound (N:=N) (a:=a) (c:=c) (mode:=mode) (H θ) (hHs θ) G D s hc hN hbase hchar j hj S u
    (literalRawScale G s X) T (literalRawScale_pos G s hc X hX) hT cut hcut
  have hleft : (∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          angularRawDualKernelTerm ℓ (H θ) (literalRawScale G s X) 1 completedRamifiedStep
            (angularLiteralRawCoefficient ℓ G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        angularLiteralDyadicBlock ℓ G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0 := by
    simp only [angularRawDualKernelTerm,hlink,angularLiteralDyadicBlock,angularLiteralRawSeries]
  rw [hleft] at hh
  apply hh.trans
  have hsemi' := mul_le_mul_of_nonneg_left (hsemi θ) hC.le
  have hrest : 0≤(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by positivity
  calc
    _ = (C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (H θ))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) := by ring
    _ ≤ (C*(C₁*(1+‖θ‖)^degree))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) :=
      mul_le_mul_of_nonneg_right hsemi' hrest
    _ = _ := by ring


end
end InverseReflectedArithmeticHeight
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
