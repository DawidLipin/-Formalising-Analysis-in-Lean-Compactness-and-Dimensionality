import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.FiniteDimension

/-!
# Formalising Analysis in Lean: Compactness and Dimensionality

In this file we define and prove the theorem states that
for a normed vector space, the closed unit ball
is compact if and only if the vector space is finite dimensional.
We also prove Riesz's lemma as it is needed to prove the main theorem.


## Main results

- `riesz_lemma_norm`: riesz lemma for normed vector spaces.
- `compact_ball_iff_dim_fin`: theorem stating that a normed vector space
  is finite dimensional if and only if the closed unit ball is compact.
-/


-- lemma iInf_scalar_mul and norm_leq_inf_div_eps were written
-- and partially proved by Prof. Kevin Buzzard

/-- Proves property of multiplication by constant for infimum --/
lemma iInf_scalar_mul
    {ι : Type*} (f : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ⨅ i, (f i * c) = (⨅ i, f i) * c := by
  exact (Real.iInf_mul_of_nonneg hc fun i ↦ f i).symm

/--
Proof that for a fixed x, infimum with respect to y of ‖x-y‖ is less than
‖x-z‖ for any z in Y.
--/
lemma iInf_leq_all
    {𝕜 : Type u_1} [NormedField 𝕜]
    {X : Type} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Subspace 𝕜 X} {x : X} : ∀ z : Y, ⨅ y : Y, ‖x-y‖ ≤ ‖x-z‖ := by
  intro z
  refine ciInf_le ?_ z
  use 0
  intro r
  rintro ⟨y, rfl⟩
  simp only [norm_nonneg]

/--
Proof that for any small ε > 0 and x not in Y, there exists a y' in Y such that
‖x-y'‖ is less than infimum of ‖x-y‖ (with respect to y) divided by 1-ε.
Used in proof of norm_ineq_iInf_eps.
--/
lemma norm_leq_iInf_div_eps
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Subspace ℝ X} (hFc : IsClosed (Y : Set X))
    (x' : X) (hF : x' ∉ Y)
    (ε : ℝ ) (hε : ε > 0) (hε2 : ε < 1):
    ∃ y' : Y, ‖x'-y'‖ ≤ ⨅ y : Y, ‖x'-y‖/(1-ε) := by
  have := exists_lt_of_ciInf_lt (f := fun (y : Y) =>
      ‖x' - y‖ * (1 - ε)) (a := ⨅ y : Y, ‖x'-y‖) ?_
  · rcases this with ⟨i, hi⟩
    use i
    have h1 : ⨅ (y : Y), ‖x' - ↑y‖ / (1 - ε) =
        (⨅ (y : Y), ‖x' - ↑y‖) / (1 - ε) := by
      simp only [div_eq_mul_inv]
      apply iInf_scalar_mul
      simp [hε2.le]
    rw [h1, le_div_iff (by linarith)]
    exact hi.le
  · suffices (⨅ (y : Y), ‖x' - ↑y‖ * (1 - ε)) < (⨅ (y : Y), ‖x' - ↑y‖) * 1 by
      simpa
    have h1 : (1 - ε) < 1 := by linarith
    suffices (⨅ (y : Y), ‖x' - ↑y‖) * (1 - ε) = ⨅ (y : Y), ‖x' - ↑y‖ * (1 - ε) by
      skip
      rw [← this]
      suffices 0 < (⨅ (y : Y), ‖x' - ↑y‖) by
        apply mul_lt_mul_of_pos_left h1 this
      have h2 : 0 ≤ ⨅ y : Y, ‖x' - y‖ := by
        apply Real.iInf_nonneg
        exact (fun y ↦ norm_nonneg (x' - ↑y))
      have h3 : ⨅ (y : Y), ‖x' - ↑y‖ ≠ 0 := by
        have h5 := hFc.not_mem_iff_infDist_pos (x := x') (Submodule.nonempty Y)
        apply h5.1 at hF
        have h6 : Metric.infDist x' ↑Y ≠ 0 := by
          exact ne_of_gt hF
        rw [Metric.infDist_eq_iInf] at h6
        have h7 : ∀ a b : X, ‖a - b‖ = dist a b := by
            intros; exact mem_sphere_iff_norm.mp rfl
        simp_rw [h7]
        exact h6
      exact Ne.lt_of_le (id (Ne.symm h3)) h2
    symm
    apply iInf_scalar_mul
    linarith
  done

/--
Proof that the infimum norm of a difference is less than norm of difference
of any two elements and that norm of difference is less than infimum norm
divided by 1-ε.
Used in proof of riesz_lemma_norm.
--/
lemma norm_ineq_iInf_eps
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Subspace ℝ X}
    (hFc : IsClosed (Y : Set X)) (x' : X) (hF : x' ∉ Y)
    (ε : ℝ ) (hε : ε > 0) (hε2 : ε < 1):
    ∃ y' : Y, ‖x'-y'‖ ≤ ⨅ y : Y, ‖x'-y‖/(1-ε) := by
  have lemma0 := norm_leq_iInf_div_eps hFc x' hF ε hε hε2
  cases' lemma0 with y' hy'
  use y'


/--
Proof that the norm of normalized x is 1.
Used in proof of riesz_lemma_norm.
--/
lemma norm_of_normalized
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (x : X) (h1 : ‖x‖ ≠ 0):
    ‖(1/‖x‖) • (x)‖ = 1 := by
  rw [norm_smul]
  simp only [one_div, norm_inv, norm_norm]
  exact inv_mul_cancel h1

/--
Proof that norm distance between y' in Y and x not in Y is not 0.
Used in proof of riesz_lemma_norm and eps_leq_normal_diff.
--/
lemma norm_dist_ne_0
    {𝕜 : Type u_1} [NormedField 𝕜]
    {X : Type} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {Y : Subspace 𝕜 X} (x' : X)
    (hF : x' ∉ Y) (y' : Y):
    ‖x'-y'.val‖ ≠ 0 := by
  simp only [norm_ne_zero_iff, NNReal.ne_iff]
  have h1 : x' ≠ y'.val := by
    by_contra h1
    rw [h1] at hF
    exact hF y'.property
  exact sub_ne_zero.mpr h1

/--
Proof that under the assumptions of norm_dist_ne_0, the norm of
the difference of normalized x'-y' and y for any y is greater than 1-ε
for any small ε>0.
Used in proof of riesz_lemma_norm.
--/
lemma eps_leq_normal_diff
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Subspace ℝ X} (x' : X)
    (hF : x' ∉ Y) (y' : Y) (ε : ℝ ) (hε2 : ε < 1)
    (ht : ‖x'-y'‖ ≤ ⨅ y : Y, ‖x'-y‖/(1-ε)):
    ∀ y : Y, 1 - ε ≤ ‖(1/‖x'-y'‖) • (x' - y')-y‖ := by
  -- Most of this code is a simple manipulation of equations as
  -- it follows directly by rearranging second part of ht iInf_leq_all
  -- and the fact that (y' + ‖x' - ↑y'‖ • y) ∈ Y
  intro y

  -- Prove statments needed for assumptions of further lemmas
  -- and to simplify the goal
  have h3 : ‖x'-y'.val‖ ≠ 0 := norm_dist_ne_0 x' hF y'
  have h4 : ‖(1/‖x'-y'‖) • (x' - y')-y‖
      = ‖((1/‖x'-y'‖) • (x' - y'.val))-(((1/‖x'-y'.val‖) * ‖x' - y'.val‖) • y)‖
      := by
    simp only [one_div, norm_inv, norm_norm, inv_mul_cancel h3, one_smul]
  rw [h4]
  clear h4
  rw [smul_sub, mul_smul]
  simp_rw [← smul_sub, norm_smul]
  simp only [one_div, norm_inv, norm_norm]
  -- Use iInf_leq_all to obtain inequality that together with h2 will
  -- prove the statment
  have h5 : ∀ y2 : Y, ⨅ y3 : Y, ‖x'-y3‖ ≤ ‖x'-y2‖ := by
    exact iInf_leq_all
  rw [sub_sub]
  -- Use (↑y' + ‖x' - ↑y'‖ • ↑y) ∈ Y for y2 in h5 to then after changing the left
  -- hand side using h2 divide by ‖x' - ↑y'‖ and obtain the solution
  specialize h5 (↑y' + ‖x' - ↑y'‖ • ↑y)
  have h6 : (1-ε) > 0 := by
    exact sub_pos.mpr hε2
  have h7 : (1 - ε) * ‖x' - ↑y'‖ ≤ ‖x' - ↑(y' + ‖x' - ↑y'‖ • y)‖ := by
    rw [← mul_le_mul_left h6] at ht
    have h7_1 : ⨅ (y : Y), ‖x' - ↑y‖ / (1 - ε) = (⨅ (y : Y), ‖x' - ↑y‖) / (1 - ε) := by
      simp only [div_eq_mul_inv]
      apply iInf_scalar_mul
      simp [hε2.le]
    rw [h7_1, mul_div, (mul_comm (1 - ε) (⨅ (y : Y), ‖x' - ↑y‖)), ← mul_div, div_self, mul_one] at ht
    -- Obtained an extra goal from div_self
    · exact le_trans ht h5
    · exact ne_of_gt h6
  have h9 : 0 ≤ ‖x' - ↑y'‖⁻¹ := by
    exact inv_nonneg.mpr (norm_nonneg (x' - ↑y'))
  have h10 :  (1 - ε) ≤ ‖x' - ↑y'‖⁻¹ * ‖x' - ↑(y' + ‖x' - ↑y'‖ • y)‖ := by
    rw [mul_comm] at h7
    have h10_1 : ‖x' - ↑y'‖⁻¹ * ‖x' - ↑y'‖ * (1 - ε) ≤
        ‖x' - ↑y'‖⁻¹ * ‖x' - ↑(y' + ‖x' - ↑y'‖ • y)‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h7 h9
    rw [inv_mul_cancel h3, one_mul] at h10_1
    exact h10_1
  exact h10


/--
Proof of the Riesz's lemma for normed vector spaces. States that for any closed
strict subspace Y of X the exists x not in Y such that the norm of x is 1 and
the distance between x and any element of Y is greater than 1-ε for any small ε>0.
Used in proof of g_riesz_next and g_riesz_next_spec.
--/
theorem riesz_lemma_norm
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Subspace ℝ X}
    (hFc : IsClosed (Y : Set X)) (hF : ∃ z : X, z ∉ Y)
    (ε : ℝ) (hε : ε > 0) (hε2 : ε < 1):
    ∃ x : X, x ∉ Y ∧ ‖x‖=1 ∧ ⨅ y : Y, ‖x-y‖ ≥ 1-ε := by
  -- Most important parts of this proof have been proven above
  cases' hF with x' hx'
  have corr_iInf : ∃ y' : Y, ‖x'-y'‖ ≤ ⨅ y : Y, ‖x'-y‖/(1-ε) :=
    norm_ineq_iInf_eps hFc x' hx' ε hε hε2
  cases' corr_iInf with y' hy'
  -- Consider x = (1/‖x'-y'.val‖) • (x' - y'.val), with x' obtained from hF and
  -- y' from theorem proven above (norm_ineq_iInf_eps)
  use (1/‖x'-y'.val‖) • (x' - y'.val)
  have x_minus_y_ne_0 : ‖x'-y'.val‖ ≠ 0 := norm_dist_ne_0 x' hx' y'
  have norm_div_one : ‖(1/‖x'-y'.val‖) • (x' - y'.val)‖ = 1 :=
    norm_of_normalized (x' - y'.val) x_minus_y_ne_0
  -- We prove the three statements separately
  constructor
  -- First statement follows from the fact that (x' - ↑y') ∉ Y with we prove below
  · have h2 : (x' - ↑y') ∉ Y := by
      by_contra h1
      have h5 : x' ∈ Y := by
        simp only [Submodule.coe_mem y', Submodule.add_mem,
            (Submodule.sub_mem_iff_left Y y'.property).mp h1]
      exact hx' h5
    intro h3
    apply h2
    have h4 : (1 / ‖x' - ↑y'‖) ≠ 0 := by exact one_div_ne_zero x_minus_y_ne_0
    have : (IsScalarTower ℝ ℝ X) := by exact Real.isScalarTower
    exact (Submodule.smul_mem_iff Y h4).mp h3
  · constructor
    -- Second statement follows from properties of the norm
    · exact norm_div_one
    -- Thrid statement follows from eps_leq_normal_diff which we porved above
    · have norm_ge_eps : ∀ y : Y, ‖(1/‖x'-y'.val‖) • (x' - y'.val)-y‖ ≥ 1-ε :=
        fun y ↦ eps_leq_normal_diff x' hx' y' ε hε2 hy' y
      exact le_ciInf norm_ge_eps

/--
Proof that Y given by the span of all previous element in a sequence
is finite dimensional.
Used in g_riesz_next and g_riesz_next_spec.
--/
lemma fin_dim_Y_span_riesz
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ℕ) (g' : (m : ℕ) → m < k → X) :
    let Y : Subspace ℝ X := Submodule.span ℝ {x | ∃ i : {i : ℕ // i < k}, g' i.val i.property = x}
    FiniteDimensional ℝ Y := by
  intro Y
  have h : Set.Finite {x | ∃ i : {i : ℕ // i < k}, g' i.val i.property = x} := by
    apply Set.Finite.of_surjOn (s := ⊤) (f := fun (i :  {i : ℕ // i < k}) => g' i.val i.property)
    · rintro z ⟨i, rfl⟩
      use i
      simp
    · exact Set.toFinite _
  let F : Finset X := h.toFinset
  have hY : Y = Submodule.span ℝ F := by rw [Set.Finite.coe_toFinset]
  rw [hY]
  apply FiniteDimensional.span_finset


/--
Proof that if X is not finite dimentional then for Y given by the span
of all previous element in a sequence there exists an element not in Y.
Used in g_riesz_next and g_riesz_next_spec.
--/
lemma strict_sub_Y_span_riesz
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_inf : ¬FiniteDimensional ℝ X) (k : ℕ) (g' : (m : ℕ) → m < k → X) :
    let Y : Subspace ℝ X := Submodule.span ℝ {x | ∃ i : {i : ℕ // i < k}, g' i.val i.property = x}
    ∃ z, z ∉ Y := by
  intro Y
  have hY_not_fin: FiniteDimensional ℝ Y := fin_dim_Y_span_riesz k g'
  have h1 : Y ≠ ⊤ := by
    intro h
    rw [h] at hY_not_fin
    apply h_inf
    unfold FiniteDimensional
    rw [Module.finite_def]
    exact Module.Finite.iff_fg.mp hY_not_fin
  contrapose! h1
  exact Submodule.eq_top_iff'.mpr h1


-- g_riesz_next, g_riesz_next_spec, g_riesz, g_riesz_spec and g_riesz_spec1
-- were written and partially proven by Dr. Bhavik Mehta.


/--
Definition of a function with properties
needed to construct g_riesz.
Used to define g_riesz.
--/
noncomputable def g_riesz_next
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_inf : ¬FiniteDimensional ℝ X) (ε : ℝ) (hε : ε > 0)
    (hε2 : ε < 1) (k : ℕ) (g' : (m : ℕ) → m < k → X) : X :=
  let Y : Subspace ℝ X := Submodule.span ℝ {x | ∃ i : {i : ℕ // i < k}, g' i.val i.property = x}
  -- Statment below is needed for hY' but never called directly
  have _: FiniteDimensional ℝ Y := fin_dim_Y_span_riesz k g'
  have hY : ∃ z, z ∉ Y := strict_sub_Y_span_riesz h_inf k g'
  have hY' : IsClosed (Y : Set X) := Submodule.closed_of_finiteDimensional Y
  have := riesz_lemma_norm hY' hY ε hε hε2
  this.choose

/--
Proof of properties of g_riesz_next obtained from
the statement of Riesz's lemma.
Used in proof of g_riesz_spec1, g_riesz_spec2 and g_riesz_spec3.
--/
lemma g_riesz_next_spec
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_inf : ¬FiniteDimensional ℝ X) (ε : ℝ) (hε : ε > 0)
    (hε2 : ε < 1) (k : ℕ) (g' : (m : ℕ) → m < k → X) :
    let Y : Subspace ℝ X := Submodule.span ℝ {x | ∃ i : {i : ℕ // i < k}, g' i.val i.property = x}
    g_riesz_next h_inf ε hε hε2 k g' ∉ Y ∧ ‖g_riesz_next h_inf ε hε hε2 k g'‖ = 1 ∧
    ⨅ y : Y, ‖g_riesz_next h_inf ε hε hε2 k g' - y‖ ≥ 1-ε := by
  intro Y
  -- Statment below is needed for hY' but never called directly
  have _: FiniteDimensional ℝ Y := fin_dim_Y_span_riesz k g'
  have hY : ∃ z, z ∉ Y := strict_sub_Y_span_riesz h_inf k g'
  have hY' : IsClosed (Y : Set X) := Submodule.closed_of_finiteDimensional Y
  have := riesz_lemma_norm hY' hY ε hε hε2
  exact this.choose_spec

/--
Definition of a function representing a sequence
constructed using g_riesz_next.
Used in g_riesz_spec, g_riesz_spec1, g_riesz_spec2, g_riesz_spec3
f_dist_eps, dim_inf_implies_not_compact, .
--/
noncomputable def g_riesz
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_inf : ¬FiniteDimensional ℝ X) (ε : ℝ) (hε : ε > 0)
    (hε2 : ε < 1) : ℕ → X :=
  fun n => Nat.strongRec (g_riesz_next h_inf ε hε hε2) n

/--
Proof that g_reisz can be constructed using g_riesz_next
Used in g_riesz_spec1, g_riesz_spec2, g_riesz_spec3.
--/
lemma g_riesz_spec
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_inf : ¬FiniteDimensional ℝ X) (ε : ℝ) (hε : ε > 0)
    (hε2 : ε < 1) (n : ℕ) :
    g_riesz h_inf ε hε hε2 n = g_riesz_next h_inf ε hε hε2 n (fun k _ => g_riesz h_inf ε hε hε2 k) := by
  rw [g_riesz, Nat.strongRec_eq]
  rfl

/--
Proof that g_reisz has the first property given by Riesz's lemma.
Unused but included for completeness.
--/
lemma g_riesz_spec1
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_inf : ¬FiniteDimensional ℝ X) (ε : ℝ) (hε : ε > 0)
    (hε2 : ε < 1) (n : ℕ) :
    let Y : Subspace ℝ X := Submodule.span ℝ {x | ∃ i : {i : ℕ // i < n}, g_riesz h_inf ε hε hε2 i.val = x}
    g_riesz h_inf ε hε hε2 n ∉ Y := by
  intro Y
  rw [g_riesz_spec]
  exact (g_riesz_next_spec h_inf ε hε hε2 n (fun k _ => g_riesz h_inf ε hε hε2 k)).1

/--
Proof that g_reisz has the second property given by Riesz's lemma.
Used in dim_inf_implies_not_compact
--/
lemma g_riesz_spec2
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_inf : ¬FiniteDimensional ℝ X) (ε : ℝ) (hε : ε > 0)
    (hε2 : ε < 1) (n : ℕ) :
    ‖g_riesz h_inf ε hε hε2 n‖=1 := by
  rw [g_riesz_spec]
  exact (g_riesz_next_spec h_inf ε hε hε2 n (fun k _ => g_riesz h_inf ε hε hε2 k)).2.1

/--
Proof that g_reisz has the third property given by Riesz's lemma.
Used in f_dist_eps.
--/
lemma g_riesz_spec3
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_inf : ¬FiniteDimensional ℝ X) (ε : ℝ) (hε : ε > 0)
    (hε2 : ε < 1) (n : ℕ) :
    let Y : Subspace ℝ X := Submodule.span ℝ {x | ∃ i : {i : ℕ // i < n}, g_riesz h_inf ε hε hε2 i.val = x}
    ⨅ y : Y, ‖g_riesz h_inf ε hε hε2 n - y‖ ≥ 1-ε := by
  intro Y
  rw [g_riesz_spec]
  exact (g_riesz_next_spec h_inf ε hε hε2 n (fun k _ => g_riesz h_inf ε hε hε2 k)).2.2


/--
Proof any two elements in the sequence given by g_riesz are at least 1/2 apart.
Version with inequality. Used to proof the version with not equal.
Used in f_dist_eps_eq.
--/
lemma f_dist_eps_leq
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_dim : ¬FiniteDimensional ℝ X):
    let f : ℕ → X := g_riesz h_dim (1/2 : ℝ) (by norm_num) (by norm_num)
    ∀ n m : ℕ, n < m → ‖f n - f m‖ ≥ 1/2 := by
  intros f n m
  let Y : Subspace ℝ X := Submodule.span ℝ {x | ∃ i : {i : ℕ // i < m},
      g_riesz h_dim (1/2 : ℝ) (by norm_num) (by norm_num) i.val = x}
  have h1 : ⨅ y : Y, ‖f m - y‖ ≥ 1-(1/2) := by
    exact g_riesz_spec3 h_dim (1/2 : ℝ) (by norm_num) (by norm_num) m
  intro h2
  have h3 : f n ∈ Y := by
    apply Submodule.subset_span
    use ⟨n, h2⟩
  rw [norm_sub_rev (f n) (f m)]
  have h5 :  ⨅ y : Y, ‖f m - y‖ ≤ ‖f m - f n‖ := by
    exact (fun z ↦ iInf_leq_all z) ⟨ (f n), h3⟩
  norm_num at h1
  exact le_trans h1 h5


/--
Proof any two elements in the sequence given by g_riesz are at least 1/2 apart.
Used in dim_inf_implies_not_compact.
--/
lemma f_dist_eps_eq
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h_dim : ¬FiniteDimensional ℝ X):
    let f : ℕ → X := g_riesz h_dim (1/2 : ℝ) (by norm_num) (by norm_num)
    ∀ n m : ℕ, n ≠ m → ‖f n - f m‖ ≥ 1/2 := by
  intros f n m
  intro h2
  apply ne_iff_lt_or_gt.1 at h2
  cases' h2 with h2 h3
  · exact f_dist_eps_leq h_dim n m h2
  · simp only [gt_iff_lt] at h3
    rw [norm_sub_rev (f n) (f m)]
    exact f_dist_eps_leq h_dim m n h3



/--
Proof any in an infinite dimensional normed space the closed unit ball is not compact.
Used in compact_ball_iff_dim_fin.
--/
theorem dim_inf_implies_not_compact
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]:
    ¬FiniteDimensional ℝ X → ¬IsCompact (Metric.closedBall (0 : X) 1) := by
  intro h_dim
  -- We prove the statement by contradiction using the fact that
  -- compactness implies sequential compactness
  by_contra h_ball
  have h_seqcomp : IsSeqCompact (Metric.closedBall (0 : X) 1) := by
    exact IsCompact.isSeqCompact h_ball
  unfold IsSeqCompact at h_seqcomp
  let f : ℕ → X := g_riesz h_dim (1/2 : ℝ) (by norm_num) (by norm_num)
  have f_norm_1 : ∀ n : ℕ, ‖f n‖ = 1 := by
    intro n
    exact g_riesz_spec2 h_dim (1/2 : ℝ) (by norm_num) (by norm_num) n
  have f_dist_eps : ∀ n m : ℕ, n ≠ m → ‖f n - f m‖ ≥ 1/2 :=
    by exact f_dist_eps_eq h_dim
  have h4 : ∀ n : ℕ, f n ∈ Metric.closedBall (0 : X) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, f_norm_1, le_refl, forall_const]
  specialize h_seqcomp h4
  rcases h_seqcomp with ⟨a, _, g, h7 ,h8⟩
  -- We show that the subsequnce is not Cauchy and hence not convergent
  have h9 : ¬CauchySeq ((fun n ↦ f n) ∘ g) := by
    simp only [Metric.cauchySeq_iff, not_forall, not_exists, not_lt]
    have h_eps_05 : (1/2 : ℝ) > 0  := by norm_num
    use (1/2), h_eps_05
    intro m
    have hm : m ≥ m  := by linarith
    have hm1 : m+1 ≥ m  := by linarith
    use  m, hm, (m+1), hm1
    rw [dist_eq_norm]
    clear hm hm1 h_eps_05
    have h12 : g m ≠ g (m+1) := by
      unfold StrictMono at h7
      have h13 : m < (m+1) := by linarith
      specialize h7 h13
      exact h7.ne
    apply f_dist_eps at h12
    exact h12
  have h10 : Filter.Tendsto ((fun n ↦ f n) ∘ g) Filter.atTop (nhds a) →
      CauchySeq ((fun n ↦ f n) ∘ g) := by
    exact fun _ ↦ Filter.Tendsto.cauchySeq h8
  apply h10 at h8
  exact h9 h8

/--
Proof any in a finite dimensional normed space the closed unit ball is compact.
Used in compact_ball_iff_dim_fin.
--/
theorem findim_implies_compact
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]:
    FiniteDimensional ℝ X → IsCompact (Metric.closedBall (0 : X) 1) := by
  intro h_dim
  have _ : ProperSpace X := by
    exact FiniteDimensional.proper_real X
  exact isCompact_closedBall 0 1

/--
Proof that a normed vector space is finite dimensional if and only if
the closed unit ball is compact.
Final theorem of this Project.
--/
theorem compact_ball_iff_dim_fin
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]:
    FiniteDimensional ℝ X ↔ IsCompact (Metric.closedBall (0 : X) 1) := by
  constructor
  · intro h1
    exact findim_implies_compact h1
  · contrapose
    exact dim_inf_implies_not_compact
