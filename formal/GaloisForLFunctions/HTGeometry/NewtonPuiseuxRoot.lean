import GaloisForLFunctions.HTGeometry.NewtonMinimalSlope
import GaloisForLFunctions.HTGeometry.TschirnhausShift
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Newton–Puiseux: every monic polynomial over `K⟦t⟧` has a ramified power-series root

Over an algebraically closed field of characteristic zero, every monic polynomial of positive
degree over `K⟦t⟧` acquires a root in `K⟦t⟧` after the ramification `t = s ^ N` for some `N ≥ 1`.
Equivalently, its roots are Puiseux series.

The induction is on the degree, and the three moves are the ones already built:

* a root of the special fibre of multiplicity below the degree splits off a monic factor of
  strictly smaller degree (`exists_monic_factor_of_rootMultiplicity`);
* otherwise the fibre is a single linear factor raised to the full degree, and translating by that
  root (`Polynomial.taylor`) followed by the Tschirnhaus shift (`exists_taylor_coeff_eq_zero`)
  makes the fibre `X ^ d` with vanishing second coefficient;
* the minimal Newton slope (`exists_newton_slope`) then transforms the polynomial
  (`newtonTransform`) into one whose fibre still has vanishing second coefficient but is no longer
  `X ^ d` — so in characteristic zero it is not a single linear factor raised to the full degree
  either, and the first move applies with a strictly smaller factor.

Ramifications compose: a further expansion of a transform is again a transform
(`map_expand_newtonTransform`), which is what lets the recursive call's ramification be pulled back
through the substitution.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type} [Field K]

/-- Expansion multiplies the order of divisibility by a power of the variable. -/
theorem expand_dvd_X_pow {N k : ℕ} (hN : N ≠ 0) {φ : PowerSeries K}
    (h : (PowerSeries.X : PowerSeries K) ^ k ∣ φ) :
    (PowerSeries.X : PowerSeries K) ^ (N * k) ∣ PowerSeries.expand N hN φ := by
  obtain ⟨ψ, hψ⟩ := h
  refine ⟨PowerSeries.expand N hN ψ, ?_⟩
  rw [hψ, map_mul, map_pow, PowerSeries.expand_X, ← pow_mul]

/-- A monic polynomial of degree `d` with a root of multiplicity `d` is the corresponding power. -/
theorem eq_X_sub_C_pow_of_rootMultiplicity {F : K[X]} (hF : F.Monic) {c : K}
    (hmult : F.rootMultiplicity c = F.natDegree) :
    F = ((X : K[X]) - Polynomial.C c) ^ F.natDegree := by
  obtain ⟨b, hb⟩ := pow_rootMultiplicity_dvd F c
  rw [hmult] at hb
  have hpow : (((X : K[X]) - Polynomial.C c) ^ F.natDegree).Monic := (monic_X_sub_C c).pow _
  have hbmonic : b.Monic := hpow.of_mul_monic_left (hb ▸ hF)
  have hdeg : F.natDegree = F.natDegree + b.natDegree := by
    conv_lhs => rw [hb]
    rw [hpow.natDegree_mul hbmonic, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
      mul_one]
  have hb0 : b.natDegree = 0 := by omega
  have hb1 : b = 1 := eq_one_of_monic_natDegree_zero hbmonic hb0
  rw [hb1, mul_one] at hb
  exact hb

/-- **Newton–Puiseux.**  Over an algebraically closed field of characteristic zero, every monic
polynomial of positive degree over `K⟦t⟧` has a root in `K⟦t⟧` after a ramification `t = s ^ N`. -/
theorem exists_isRoot_map_expand [IsAlgClosed K] [CharZero K] (d : ℕ) :
    ∀ f : (PowerSeries K)[X], f.Monic → f.natDegree = d → 0 < d →
      ∃ (N : ℕ) (hN : N ≠ 0) (y : PowerSeries K),
        (f.map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot y := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro f hf hdeg hd
    classical
    -- a factor of strictly smaller positive degree suffices
    have hfactor : ∀ g h : (PowerSeries K)[X], g.Monic → f = g * h → 0 < g.natDegree →
        g.natDegree < d →
        ∃ (N : ℕ) (hN : N ≠ 0) (y : PowerSeries K),
          (f.map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot y := by
      intro g h hg hfgh hgpos hglt
      obtain ⟨N, hN, y, hy⟩ := ih g.natDegree hglt g hg rfl hgpos
      refine ⟨N, hN, y, ?_⟩
      rw [hfgh, Polynomial.map_mul, Polynomial.IsRoot, Polynomial.eval_mul, hy, zero_mul]
    -- the special fibre
    have hFmonic : (f.map (PowerSeries.constantCoeff (R := K))).Monic := hf.map _
    have hFdeg : (f.map (PowerSeries.constantCoeff (R := K))).natDegree = d := by
      rw [hf.natDegree_map, hdeg]
    obtain ⟨c, hc⟩ : ∃ c : K, (f.map (PowerSeries.constantCoeff (R := K))).IsRoot c := by
      refine IsAlgClosed.exists_root _ ?_
      rw [Polynomial.degree_eq_natDegree hFmonic.ne_zero, hFdeg]
      exact_mod_cast (by omega : d ≠ 0)
    set m : ℕ := (f.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity c with hm
    have hmpos : 0 < m := (Polynomial.rootMultiplicity_pos hFmonic.ne_zero).2 hc
    rcases Nat.lt_or_ge m d with hmlt | hmge
    · -- the fibre root does not have full multiplicity: split off a smaller factor
      obtain ⟨g, h, hg, _, hgdeg, hfgh⟩ := exists_monic_factor_of_rootMultiplicity hf c
      exact hfactor g h hg hfgh (by rw [hgdeg]; exact hmpos) (by rw [hgdeg]; exact hmlt)
    · -- the fibre is a single linear factor raised to the full degree
      have hmle : m ≤ d := by
        have hdvdm := pow_rootMultiplicity_dvd (f.map (PowerSeries.constantCoeff (R := K))) c
        have hnd := Polynomial.natDegree_le_of_dvd hdvdm hFmonic.ne_zero
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one, hFdeg] at hnd
        rw [hm]
        exact hnd
      have hmd : m = d := le_antisymm hmle hmge
      have hFpow : f.map (PowerSeries.constantCoeff (R := K))
          = ((X : K[X]) - Polynomial.C c) ^ d := by
        have := eq_X_sub_C_pow_of_rootMultiplicity hFmonic (by rw [← hm, hmd, hFdeg])
        rwa [hFdeg] at this
      -- translate the root to the origin
      set f₁ : (PowerSeries K)[X] := Polynomial.taylor (PowerSeries.C c) f with hf₁
      have hf₁monic : f₁.Monic := monic_taylor hf _
      have hf₁deg : f₁.natDegree = d := by rw [hf₁, Polynomial.natDegree_taylor, hdeg]
      have hf₁fib : f₁.map (PowerSeries.constantCoeff (R := K)) = (X : K[X]) ^ d := by
        rw [hf₁, map_taylor, PowerSeries.constantCoeff_C, hFpow, Polynomial.taylor_apply]
        have hcomp : (((X : K[X]) - Polynomial.C c) ^ d).comp ((X : K[X]) + Polynomial.C c)
            = ((X : K[X]) + Polynomial.C c - Polynomial.C c) ^ d := by
          rw [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
        rw [hcomp, add_sub_cancel_right]
      -- remove the second coefficient
      obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hchar : ((e + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hf₁e : PowerSeries.constantCoeff (f₁.coeff e) = 0 := by
        have := congrArg (fun p => Polynomial.coeff p e) hf₁fib
        simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow] at this
        rw [this, if_neg (by omega)]
      obtain ⟨a, hacoeff, hazero⟩ :=
        exists_taylor_coeff_eq_zero hf₁monic (by rw [hf₁deg, he]) hchar
      have haconst : PowerSeries.constantCoeff a = 0 := by
        rw [hacoeff, hf₁e, neg_zero, zero_mul]
      set f₂ : (PowerSeries K)[X] := Polynomial.taylor a f₁ with hf₂
      have hf₂monic : f₂.Monic := monic_taylor hf₁monic _
      have hf₂deg : f₂.natDegree = d := by rw [hf₂, Polynomial.natDegree_taylor, hf₁deg]
      have hf₂fib : f₂.map (PowerSeries.constantCoeff (R := K)) = (X : K[X]) ^ d := by
        rw [hf₂, map_taylor, haconst, hf₁fib, Polynomial.taylor_apply, Polynomial.C_0, add_zero,
          Polynomial.comp_X]
      have hf₂fibcoeff : ∀ i < d, PowerSeries.constantCoeff (f₂.coeff i) = 0 := by
        intro i hi
        have := congrArg (fun p => Polynomial.coeff p i) hf₂fib
        simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow] at this
        rw [this, if_neg (by omega)]
      have hf₂e : f₂.coeff e = 0 := hazero
      -- transfer a root back through the two translations
      have htransfer : ∀ (N : ℕ) (hN : N ≠ 0) (y : PowerSeries K),
          (f₂.map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot y →
          ∃ (N' : ℕ) (hN' : N' ≠ 0) (y' : PowerSeries K),
            (f.map (PowerSeries.expand (R := K) N' hN').toRingHom).IsRoot y' := by
        intro N hN y hy
        refine ⟨N, hN, y + (PowerSeries.expand (R := K) N hN).toRingHom a
          + (PowerSeries.expand (R := K) N hN).toRingHom (PowerSeries.C c), ?_⟩
        have hstep₂ : (f₂.map (PowerSeries.expand (R := K) N hN).toRingHom)
            = Polynomial.taylor ((PowerSeries.expand (R := K) N hN).toRingHom a)
              (f₁.map (PowerSeries.expand (R := K) N hN).toRingHom) := by
          rw [hf₂, map_taylor]
        have hstep₁ : (f₁.map (PowerSeries.expand (R := K) N hN).toRingHom)
            = Polynomial.taylor ((PowerSeries.expand (R := K) N hN).toRingHom (PowerSeries.C c))
              (f.map (PowerSeries.expand (R := K) N hN).toRingHom) := by
          rw [hf₁, map_taylor]
        rw [hstep₂] at hy
        rw [isRoot_taylor_iff] at hy
        rw [hstep₁] at hy
        rw [isRoot_taylor_iff] at hy
        exact hy
      by_cases hzero : ∀ i, i < d → f₂.coeff i = 0
      · -- the polynomial is `X ^ d` and the origin is a root
        refine htransfer 1 one_ne_zero 0 ?_
        rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
          hzero 0 hd, map_zero]
      · have hex : ∃ i, i < d ∧ f₂.coeff i ≠ 0 := by
          by_contra hcon
          refine hzero fun i hi => ?_
          by_contra hci
          exact hcon ⟨i, hi, hci⟩
        obtain ⟨i₁, hi₁d, hi₁ne⟩ := hex
        obtain ⟨p, q, hq, hppos, hdvd, i₀, hi₀d, hi₀ne⟩ :=
          exists_newton_slope (f := f₂) (d := d) hf₂fibcoeff ⟨i₁, hi₁d, hi₁ne⟩
        have hdvd' : ∀ i ≤ f₂.natDegree,
            (PowerSeries.X : PowerSeries K) ^ (p * (f₂.natDegree - i)) ∣
              PowerSeries.expand q hq (f₂.coeff i) := by
          rw [hf₂deg]
          exact hdvd
        obtain ⟨T, hT⟩ : ∃ T : (PowerSeries K)[X], T = newtonTransform f₂ p q hq := ⟨_, rfl⟩
        obtain ⟨hTmonic, hTdeg⟩ := monic_newtonTransform hf₂monic p q hq
        rw [← hT] at hTmonic hTdeg
        have hTdeg' : T.natDegree = d := by rw [hTdeg, hf₂deg]
        -- the fibre of the transform: second coefficient still zero, but not `X ^ d`
        obtain ⟨G, hG⟩ : ∃ G : K[X], G = T.map (PowerSeries.constantCoeff (R := K)) := ⟨_, rfl⟩
        have hGmonic : G.Monic := by rw [hG]; exact hTmonic.map _
        have hGdeg : G.natDegree = d := by rw [hG, hTmonic.natDegree_map, hTdeg']
        have hGe : G.coeff e = 0 := by
          rw [hG, hT, coeff_map_constantCoeff_newtonTransform f₂ p q hq (by omega), hf₂e, map_zero,
            map_zero]
        have hGi₀ : G.coeff i₀ ≠ 0 := by
          rw [hG, hT, coeff_map_constantCoeff_newtonTransform f₂ p q hq (by rw [hf₂deg]; omega)]
          rw [hf₂deg]
          exact hi₀ne
        obtain ⟨c', hc'⟩ : ∃ c' : K, G.IsRoot c' := by
          refine IsAlgClosed.exists_root _ ?_
          rw [Polynomial.degree_eq_natDegree hGmonic.ne_zero, hGdeg]
          exact_mod_cast (by omega : d ≠ 0)
        have hm'pos : 0 < G.rootMultiplicity c' :=
          (Polynomial.rootMultiplicity_pos hGmonic.ne_zero).2 hc'
        have hm'lt : G.rootMultiplicity c' < d := by
          rcases Nat.lt_or_ge (G.rootMultiplicity c') d with hlt | hge'
          · exact hlt
          · exfalso
            have hmd' : G.rootMultiplicity c' = G.natDegree := by
              have hdvdm := pow_rootMultiplicity_dvd G c'
              have hnd := Polynomial.natDegree_le_of_dvd hdvdm hGmonic.ne_zero
              rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hnd
              rw [hGdeg]
              exact le_antisymm (by rwa [hGdeg] at hnd) hge'
            have hGpow : G = ((X : K[X]) - Polynomial.C c') ^ d := by
              have := eq_X_sub_C_pow_of_rootMultiplicity hGmonic hmd'
              rwa [hGdeg] at this
            have hcoeffe : G.coeff e = (-c') ^ (d - e) * (d.choose e : K) := by
              rw [hGpow, sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]
            have hde : d - e = 1 := by omega
            have hchoose : d.choose e = d := by
              rw [he, Nat.choose_succ_self_right]
            rw [hde, hchoose, pow_one] at hcoeffe
            have hc'zero : c' = 0 := by
              have hzero' : (-c') * (d : K) = 0 := by rw [← hcoeffe, hGe]
              have hdne : (d : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
              exact neg_eq_zero.mp ((mul_eq_zero.mp hzero').resolve_right hdne)
            rw [hc'zero, Polynomial.C_0, sub_zero] at hGpow
            apply hGi₀
            rw [hGpow, Polynomial.coeff_X_pow, if_neg (by omega)]
        -- split the transform and recurse on the smaller factor
        obtain ⟨g', h', hg'monic, _, hg'deg, hTfact⟩ :=
          exists_monic_factor_of_rootMultiplicity hTmonic c'
        obtain ⟨N, hN, y, hy⟩ := ih (G.rootMultiplicity c') hm'lt g' hg'monic
          (by rw [hg'deg, hG]) hm'pos
        -- the recursive ramification is again a slope substitution for `f₂`
        have hyT : (T.map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot y := by
          rw [hTfact, Polynomial.map_mul, Polynomial.IsRoot, Polynomial.eval_mul, hy, zero_mul]
        rw [hT, map_expand_newtonTransform] at hyT
        have hdvdN : ∀ i ≤ f₂.natDegree,
            (PowerSeries.X : PowerSeries K) ^ (N * p * (f₂.natDegree - i)) ∣
              PowerSeries.expand (N * q) (Nat.mul_ne_zero hN hq) (f₂.coeff i) := by
          intro i hi
          have hstep := expand_dvd_X_pow (N := N) hN (hdvd' i hi)
          rw [← PowerSeries.expand_mul N hN q hq] at hstep
          rwa [← Nat.mul_assoc] at hstep
        have hroot := isRoot_map_expand_of_isRoot_newtonTransform (f := f₂) (N * p) (N * q)
          (Nat.mul_ne_zero hN hq) hdvdN hyT
        exact htransfer (N * q) (Nat.mul_ne_zero hN hq) _ hroot

end GaloisForLFunctions.HTGeometry
