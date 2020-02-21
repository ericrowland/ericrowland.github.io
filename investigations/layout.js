// This is a JavaScript file that handles layout for the pages at http://thales.math.uqam.ca/~rowland/investigations/.

blue = "3366ff";
orange = "ff8c00";
green = "11aa00";
lightorange = "ee8c00";
lightgreen = "55e800";
slate = "222222";
black = "black";

sitesection = "default";	// which section
project = "";			// which project
textcolor = black;		// color of text
link = blue;			// color of normal links
linkcolor = lightgreen;		// color of like-paged links in the footer
titlecolor = blue;		// color of title
headerbackground = slate;	// color of background of header
suffix = "-project";		// suffix of the page (dependent on section)
function projects(string) {
  sitesection = "projects";
  project = string;
  link = green;
  titlecolor = lightgreen;
  linkcolor = lightgreen;
  suffix = "-project";
}
function expositions(string) {
  sitesection = "expositions";
  project = string;
  link = orange;
  titlecolor = lightorange;
  linkcolor = orange;
  suffix = "";
}

function bullet() {
  document.write(" <font color=" + blue + ">&bull;</font> ");
}
function endline() {
  document.write("<br>");
}
function printlink(filename, title, endoflineQ) {
  document.write("<a href=" + filename + suffix + ".html><font color=" + linkcolor + ">" + title + "</font></a>");
  if(endoflineQ) endline();
  else bullet();
}

function header(title) {
  document.write("<body bgcolor=white text=black link=" + link + " alink=" + link + " vlink=" + link + " style=\"margin:0\" leftmargin=0 rightmargin=0 topmargin=0 bottommargin=0 marginwidth=0 marginheight=0>");
  if(title != "none") document.write("<table width=100% cellspacing=0 border=0 bgcolor=black><tr><td><center><font size=1><br></font><font color=" + titlecolor + " size=6><b>" + title + "</b></font><font size=1><br>&nbsp;</font></center></table>");
  document.write("<table width=100% cellspacing=10><tr><td>");
}

function footer() {
  document.write("</table><a id=footer></a><table width=100% cellspacing=0 bgcolor=black><tr><td align=center><font size=2><b>");

  if(sitesection == "projects") document.write("<a href=index.html#projects><font color=" + lightgreen + ">Projects</font></a><img src=images/bullet.gif width=11 height=6><a href=" + project + ".html#footer><font color=" + orange + ">Exposition</font></a><br>");
  else if(sitesection == "expositions") document.write("<a href=" + project + "-project.html#footer><font color=" + lightgreen + ">Project</font></a><img src=images/bullet.gif width=11 height=6><a href=index.html#expositions><font color=" + orange + ">Expositions</font></a><br>");
  else document.write("<a href=index.html#projects><font color=" + lightgreen + ">Projects</font></a><img src=images/bullet.gif width=11 height=6><a href=index.html#expositions><font color=" + orange + ">Expositions</font></a><br>");

//  printlink("eulerline", "The Euler Line", false);
//  printlink("hyperspheres", "Hyperspheres", false);
  printlink("pascalssimplices", "Pascal's Simplices", false);
  printlink("pythagoreantriples", "Pythagorean Triples", false);
  printlink("polygons", "Regular Polygons", true);
  printlink("polyhedra", "Regular Polyhedra", false);
  printlink("polytopes", "Regular Polytopes", false);
  printlink("sumsofpowers", "Sums of Consecutive Powers", true);
  document.write("<a href=induction.html><font color=" + blue + ">Mathematical Induction</font></a>");
  bullet();
  document.write("<a href=modulararithmetic.html><font color=" + blue + ">Modular Arithmetic</font></a>");
  bullet();
  document.write("<a href=polynomialequations.html><font color=" + blue + ">Polynomial Equations</font></a>");
  endline();
  document.write("<a href=index.html><font color=" + blue + ">Investigations Home</font></a>");
  bullet();
  document.write("<a href=calculators.html><font color=" + blue + ">Calculators</font></a>");
  bullet();
  document.write("<a href=books.html><font color=" + blue + ">Popular Books</font></a>");
  endline();
  document.write("<a href=../index.html><font color=" + blue + ">Eric Rowland</font></a>");
//  document.write(", <img src=images/email.gif width=156 height=15 align=absmiddle>");

  document.write("</b></font></table>");
}
