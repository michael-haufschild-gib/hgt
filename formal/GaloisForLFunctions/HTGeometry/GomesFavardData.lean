import GaloisForLFunctions.HTGeometry.FavardJacobiMomentRealization
import GaloisForLFunctions.HTGeometry.StieltjesExistence

/-!
# Complete positive-moment reconstruction from data

Application of faithful reconstruction questions in https://arxiv.org/abs/2607.24901
and internal-frame data in https://arxiv.org/abs/2404.10461. Real diagonal data,
logarithmic lower data, and logarithmic initial mass construct positive moment
sequences without proof inputs. Conversely every positive moment sequence is
recovered from its own canonical data. The underlying triangular uniqueness law
requires no positivity at all and retains the initial mass exactly.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Positive lower recurrence coefficients, with the unused zero index fixed canonically. -/
def gomesFavardLower (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => Real.exp (q n)

/-- Arbitrary positive moment mass together with arbitrary real diagonal and log-lower data. -/
def gomesFavardMoment (r : ℝ) (a q : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp r * favardMoment a (gomesFavardLower q) n

/-- Exponentiated data discharge all moment positivity requirements internally. -/
theorem gomesFavardMoment_positive (r : ℝ) (a q : ℕ → ℝ) :
    PositiveMomentForm (gomesFavardMoment r a q) := by
  refine ⟨fun p hp => ?_⟩
  change 0 < momentFunctional (fun n => Real.exp r*favardMoment a (gomesFavardLower q) n) (p*p)
  rw [momentFunctional_smul_sequence]
  exact mul_pos (Real.exp_pos r)
    ((favard_positiveMomentForm a (gomesFavardLower q) (fun n => Real.exp_pos (q n))).pos_of_ne_zero p hp)

/-- The separate positive mass parameter is retained exactly by the zeroth moment. -/
theorem gomesFavardMoment_zero (r : ℝ) (a q : ℕ → ℝ) : gomesFavardMoment r a q 0 = Real.exp r := by
  simp [gomesFavardMoment]

/-- Annihilating the full monic recurrence family determines every moment once its initial mass is fixed. -/
theorem gomesFavard_mass_reconstruction_iff (a b s : ℕ → ℝ) :
    s = (fun n => s 0*favardMoment a b n) ↔
      ∀ n : ℕ, momentFunctional s (favardPoly a b (n+1)) = 0 := by
  constructor
  · intro he n
    rw [he,momentFunctional_smul_sequence,momentFunctional_favardPoly,mul_zero]
  · intro h
    funext m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero => simp
      | succ n =>
        let p := favardPoly a b (n+1)
        have hdeg : p.natDegree = n+1 := favardPoly_natDegree a b (n+1)
        have hsum : momentFunctional s p =
            ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i*s i := by
          rw [momentFunctional_eq_support_sum]
          exact Finset.sum_subset p.supp_subset_range_natDegree_succ
            (fun i _ hi => by rw [Polynomial.notMem_support_iff.mp hi,zero_mul])
        have hlead : p.coeff (n+1) = 1 := by
          have hc := (favardPoly_monic a b (n+1)).coeff_natDegree
          rwa [hdeg] at hc
        have hh : momentFunctional s p = 0 := h n
        rw [hsum,hdeg,Finset.sum_range_succ,hlead,one_mul] at hh
        have hs : (∑ i ∈ Finset.range (n+1), p.coeff i*s i) =
            s 0*∑ i ∈ Finset.range (n+1), p.coeff i*favardMoment a b i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [ih i (Finset.mem_range.mp hi)]
          ring
        rw [hs] at hh
        rw [favardMoment_succ]
        change s (n+1) = s 0*(-∑ i ∈ Finset.range (n+1), p.coeff i*favardMoment a b i)
        linarith

/-- Complete canonical reconstruction: a sequence is positive exactly when its own Jacobi data
and positive initial mass recover it through the concrete Favard construction. -/
theorem gomesFavard_canonical_reconstruction_iff (s : ℕ → ℝ) :
    s = gomesFavardMoment (Real.log (s 0)) (monicOrthoAlpha s)
      (fun n => Real.log (monicOrthoBeta s (n+1))) ↔ PositiveMomentForm s := by
  constructor
  · intro he
    rw [he]
    exact gomesFavardMoment_positive _ _ _
  · intro h
    have h0 : 0 < s 0 := by
      have hp := h.pos_of_ne_zero (1 : Polynomial ℝ) one_ne_zero
      simpa [momentInner_def,momentFunctional_one] using hp
    have hb : ∀ n : ℕ, 0 < monicOrthoBeta s (n+1) :=
      fun n => monicOrthoBeta_pos h (Nat.succ_pos n)
    have hpoly : ∀ n : ℕ,
        favardPoly (monicOrthoAlpha s) (gomesFavardLower (fun k => Real.log (monicOrthoBeta s (k+1)))) n =
          monicOrtho s n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        cases n with
        | zero => simp
        | succ n =>
          cases n with
          | zero =>
            have hr := X_mul_monicOrtho h 0
            simp [monicOrthoBeta,Polynomial.smul_eq_C_mul] at hr
            rw [favardPoly_one]
            linear_combination hr
          | succ n =>
            rw [favardPoly_succ_succ,ih (n+1) (by omega),ih n (by omega)]
            simp only [gomesFavardLower,Real.exp_log (hb n)]
            have hr := X_mul_monicOrtho h (n+1)
            simp only [show n+1-1=n from rfl,Polynomial.smul_eq_C_mul] at hr
            linear_combination hr
    have ha : ∀ n : ℕ, momentFunctional s
        (favardPoly (monicOrthoAlpha s) (gomesFavardLower (fun k => Real.log (monicOrthoBeta s (k+1)))) (n+1)) = 0 := by
      intro n
      rw [hpoly]
      have hh := monicOrtho_inner_eq_zero_of_degree_lt h (n+1) (n+1) le_rfl (1 : Polynomial ℝ)
        (by
          simp only [Polynomial.degree_one]
          exact_mod_cast Nat.succ_pos n)
      simpa [momentInner_def] using hh
    have he := (gomesFavard_mass_reconstruction_iff (monicOrthoAlpha s)
      (gomesFavardLower (fun k => Real.log (monicOrthoBeta s (k+1)))) s).mpr ha
    funext n
    have hn := congrFun he n
    simpa [gomesFavardMoment,Real.exp_log h0] using hn

/-- Every positive moment form is generated by data alone, with no positivity certificates among the data. -/
theorem gomesFavard_positive_iff_exists_data (s : ℕ → ℝ) :
    PositiveMomentForm s ↔ ∃ (r : ℝ) (a q : ℕ → ℝ), s = gomesFavardMoment r a q := by
  constructor
  · intro h
    exact ⟨Real.log (s 0),monicOrthoAlpha s,fun n => Real.log (monicOrthoBeta s (n+1)),
      (gomesFavard_canonical_reconstruction_iff s).mpr h⟩
  · rintro ⟨r,a,q,rfl⟩
    exact gomesFavardMoment_positive r a q

end GaloisForLFunctions.HTGeometry
