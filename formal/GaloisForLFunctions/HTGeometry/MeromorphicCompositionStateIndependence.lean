import GaloisForLFunctions.HTGeometry.CascadeStateIndependence
import GaloisForLFunctions.HTGeometry.MeromorphicPlaneAlgebra

/-!
# State independence for meromorphic-outer compositions

A transcendental meromorphic outer function and a transcendental entire inner function have
algebraically independent composition states `z`, `g z`, and `f (g z)`.

The proof uses the unbounded-fibre theorem already available for transcendental entire functions.
On a fibre of `g`, a three-state relation becomes a polynomial in `z`.  Fibres larger than its
degree kill every coefficient on a nonempty open set.  Meromorphic identity continuation then
turns those coefficient identities into a polynomial relation between the coordinate and `f`,
contradicting transcendence of the outer function over the rational coordinate field.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- A globally meromorphic function that vanishes on a nonempty open set is zero in the
meromorphic plane field. -/
theorem ofMeromorphic_eq_zero_of_eq_zero_on_open {F : ℂ → ℂ}
    (hF : ∀ z, MeromorphicAt F z) {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hzero : ∀ z ∈ U, F z = 0) :
    ofMeromorphic F hF = 0 := by
  have hmer : MeromorphicOn F (Set.univ : Set ℂ) := fun z _ => hF z
  obtain ⟨u, hu⟩ := hUne
  have hev : F =ᶠ[𝓝 u] 0 := by
    filter_upwards [hU.mem_nhds hu] with z hz
    exact hzero z hz
  have htopu : meromorphicOrderAt F u = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (Filter.Eventually.filter_mono inf_le_left hev)
  have htop : ∀ x : ℂ, meromorphicOrderAt F x = ⊤ := by
    intro x
    by_contra hx
    exact (hmer.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ x) (Set.mem_univ u) hx) htopu
  have heq : ofMeromorphic F hF =
      ofMeromorphic (fun _ : ℂ => 0) (fun z => MeromorphicAt.const 0 z) := by
    rw [ofMeromorphic_eq_iff]
    intro x
    exact meromorphicOrderAt_eq_top_iff.mp (htop x)
  exact heq

/-- Multivariate polynomial evaluation commutes with passage from globally meromorphic functions
to the meromorphic plane field. -/
theorem eval_ofMeromorphic {σ : Type*} (F : σ → ℂ → ℂ)
    (hF : ∀ i z, MeromorphicAt (F i) z) (P : MvPolynomial σ ℂ) :
    MvPolynomial.aeval (fun i => ofMeromorphic (F i) (hF i)) P =
      ofMeromorphic (fun z => MvPolynomial.eval (fun i => F i z) P)
        (fun z => by
          induction P using MvPolynomial.induction_on with
          | C a => simp
          | add p q hp hq => simpa only [map_add] using hp.fun_add hq
          | mul_X p i hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.fun_mul (hF i z)) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.aeval_C, algebraMap_plane]
      apply (ofMeromorphic_eq_iff _ _).mpr
      intro x
      exact Filter.Eventually.of_forall (fun z => by simp)
  | add p q hp hq =>
      rw [map_add, hp, hq, ofMeromorphic_add]
      apply (ofMeromorphic_eq_iff _ _).mpr
      intro x
      exact Filter.Eventually.of_forall (fun z => by simp)
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.aeval_X, hp, ofMeromorphic_mul]
      apply (ofMeromorphic_eq_iff _ _).mpr
      intro x
      exact Filter.Eventually.of_forall (fun z => by simp)

/-- Algebraic independence of the coordinate and a global meromorphic function is the exact
function-field form of transcendence over the rational coordinate field. -/
def TranscendentalMeromorphic (f : ℂ → ℂ) (hf : ∀ z, MeromorphicAt f z) : Prop :=
  AlgebraicIndependent ℂ
    ![ofMeromorphic id (fun z => (analyticAt_id (𝕜 := ℂ) (z := z)).meromorphicAt),
      ofMeromorphic f hf]

/-- **A transcendental meromorphic outer function and a transcendental entire inner function have
three algebraically independent composition states.** -/
theorem noRelation_meromorphicOuter_comp_of_transcendental
    {f g : ℂ → ℂ} (hf : ∀ z, MeromorphicAt f z)
    (hft : TranscendentalMeromorphic f hf) (hg : TranscendentalEntire g)
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0) :
    ¬ ∀ z : ℂ, MvPolynomial.eval ![z, g z, f (g z)] P = 0 := by
  intro hrel
  set Q : Polynomial (MvPolynomial (Fin 2) ℂ) := MvPolynomial.finSuccEquiv ℂ 2 P with hQdef
  have hQ0 : Q ≠ 0 := by
    intro h
    refine hP ((MvPolynomial.finSuccEquiv ℂ 2).injective ?_)
    rw [← hQdef, h, map_zero]
  obtain ⟨U, R, hU, hUne, hmany⟩ := exists_open_many_preimages hg (Q.natDegree + 1)
  have hcoeff : ∀ u ∈ U, ∀ i : ℕ, MvPolynomial.eval ![u, f u] (Q.coeff i) = 0 := by
    intro u hu i
    obtain ⟨T, hTcard, _, hTg⟩ := hmany u hu
    set p : Polynomial ℂ := Polynomial.map (MvPolynomial.eval ![u, f u]) Q with hpdef
    have hroots : ∀ x ∈ T, p.eval x = 0 := by
      intro x hx
      have hgx : g x = u := hTg x hx
      have hxrel := hrel x
      have hcons : (![x, g x, f (g x)] : Fin 3 → ℂ) = Fin.cons x ![u, f u] := by
        funext j
        fin_cases j <;> simp [hgx]
      rw [hcons, MvPolynomial.eval_eq_eval_mv_eval'] at hxrel
      rw [hpdef, hQdef]
      exact hxrel
    have hdeg : p.degree < (T.card : ℕ) := by
      by_cases hp0 : p = 0
      · rw [hp0, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe _
      · rw [Polynomial.degree_eq_natDegree hp0]
        have hle : p.natDegree ≤ Q.natDegree := by
          rw [hpdef]
          exact Polynomial.natDegree_map_le
        exact_mod_cast lt_of_le_of_lt hle (by omega)
    have hp0 : p = 0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero T hdeg hroots
    have hci := congrArg (fun q : Polynomial ℂ => q.coeff i) hp0
    simpa [hpdef, Polynomial.coeff_map] using hci
  have hcoeffField : ∀ i : ℕ,
      MvPolynomial.aeval
        ![ofMeromorphic id (fun z => (analyticAt_id (𝕜 := ℂ) (z := z)).meromorphicAt),
          ofMeromorphic f hf]
        (Q.coeff i) = 0 := by
    intro i
    let F : Fin 2 → ℂ → ℂ := ![id, f]
    have hFm : ∀ j z, MeromorphicAt (F j) z := by
      intro j z
      fin_cases j
      · exact (analyticAt_id (𝕜 := ℂ) (z := z)).meromorphicAt
      · exact hf z
    rw [show (![ofMeromorphic id (fun z => (analyticAt_id (𝕜 := ℂ) (z := z)).meromorphicAt),
        ofMeromorphic f hf] : Fin 2 → MeromorphicPlane) =
        fun j => ofMeromorphic (F j) (hFm j) by funext j; fin_cases j <;> rfl]
    rw [eval_ofMeromorphic F hFm]
    apply ofMeromorphic_eq_zero_of_eq_zero_on_open _ hU hUne
    intro u hu
    have hvec : (fun j => F j u) = ![u, f u] := by
      funext j
      fin_cases j <;> rfl
    rw [hvec]
    exact hcoeff u hu i
  refine hQ0 (Polynomial.ext ?_)
  intro i
  have hci : Q.coeff i = 0 :=
    (algebraicIndependent_iff_injective_aeval.mp hft) (by
      rw [hcoeffField i, map_zero])
  simp [hci]

end

end GaloisForLFunctions.HTGeometry
