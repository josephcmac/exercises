theory exercises1

imports Complex_Main

begin

section\<open>Easy\<close>

lemma ex1: \<open>(2::nat) + 2 = 4\<close>
  sorry
    (* use sledgehammer *)

lemma ex2: \<open>(2::nat)^3 = 8\<close>
  sorry
    (* simplify: by simp *)

lemma ex3: \<open>(n::nat) + n = 2*n\<close>
  sorry
    (* simplify *)

lemma ex4: \<open>(x::int)^2 - y^2 = (x-y)*(x+y)\<close>
  sorry
    (* use sledgehammer *)

lemma ex5: \<open>\<exists>t. (x::int)^2 - y^2 = (x + y)*t\<close>
  sorry
    (* use sledgehammer *)

lemma ex6: \<open>\<exists>t s. (x::int)^2  = s*t + y^2 \<and> s + t = 2*x\<close>
  sorry
    (* use sledgehammer *)

section\<open>Medium\<close>
lemma ex7: 
  assumes \<open>(x::nat)^2 + y^2 = z^2\<close>
  shows \<open>\<exists>t. x + y + z = 2*t\<close>
    (* complete the part that it is missing (it a little variation of the part that is is shown) *)
proof(cases \<open>even x\<close>)
  case True
  hence \<open>even x\<close>
    by blast
  hence \<open>even (x^2)\<close>
    by simp
  thus ?thesis 
  proof(cases \<open>even y\<close>)
    case True
    hence \<open>even y\<close>
      by blast
    hence \<open>even (y^2)\<close>
      by simp
    hence \<open>even (z^2)\<close>
      using \<open>even (x^2)\<close> and \<open>even (y^2)\<close> and  \<open>x^2 + y^2 = z^2\<close> by presburger
    hence \<open>even z\<close>
      by auto
    hence \<open>even (x + y + z)\<close>
      using \<open>even x\<close> and \<open>even y\<close> by auto
    thus \<open>\<exists>t. x + y + z = 2*t\<close> by blast
  next
    case False
      (* put code here *)
    thus \<open>\<exists>t. x + y + z = 2*t\<close> sorry
  qed
next
  case False
    (* put code here *)
  then show \<open>\<exists>t. x + y + z = 2*t\<close> sorry
qed

lemma ex8: 
  assumes \<open>(x::int) * y = 25\<close> and \<open>x + y = 10\<close>
  shows \<open>x = y\<close>
  sorry

lemma ex9:
  fixes x y::int
  assumes \<open>x \<noteq> 0\<close> and \<open>y \<noteq> 0\<close>
  shows \<open>\<exists>z::int. 1/x + 1/y = z/(x*y) \<and> even (x + y + z)\<close>
  sorry

section\<open>Hard (reverse engineering)\<close>

(* In this section it is forbidden to use the function sqrt, because we will apply reverse 
   engineering in order to reconstruct theorems about it *)

definition my_sqrt :: "real \<Rightarrow> real"
  where "my_sqrt x = (if x \<ge> 0 then (the_inv (\<lambda>y. y^2)) x else 0)"

lemma ex10:
  fixes x y::real
  assumes \<open>x \<ge> 0\<close>
  shows \<open>(my_sqrt x)^2 = x\<close>
  sorry

thm real_sqrt_pow2 (* ctrl + clic here in order to do reverse engineering in the file
  where sqrt is my_sqrt *)

lemma ex11:
  fixes x y::real
  assumes \<open>x \<ge> 0\<close> and \<open>y \<ge> 0\<close>
  shows \<open>my_sqrt(x*y) \<le> (x + y)/2\<close>
  sorry

thm arith_geo_mean_sqrt (* ctrl + clic here in order to do reverse engineering in the file
  where sqrt is my_sqrt *)

lemma ex12:
  fixes x y z::real
  assumes \<open>x \<ge> 0\<close> and \<open>y \<ge> 0\<close> and \<open>z \<ge> 0\<close>
  shows \<open>sqrt(x*y*z) \<le> (x + y + z)/2\<close>
    (* Try to do this one without reverse engineering *)
  sorry

end
