// This is a JavaScript file that handles layout for the pages at http://math.tulane.edu/~erowland.

blue = "3366ff";
orange = "ff8c00";
green = "11aa00";
lightorange = "ee8c00";
lightgreen = "55e800";
slate = "222222";
black = "black";

textcolor = black;		// color of text
link = blue;			// color of normal links
linkcolor = lightgreen;		// color of like-paged links in the footer
titlecolor = blue;		// color of title
headerbackground = slate;	// color of background of header

function bullet() {
  document.write(" <font color=" + blue + ">&bull;</font> ");
}
function endline() {
  document.write("&nbsp;");
  document.write("<br>");
}

function toplinks(prefix) {
  document.write("<td align=right><font size=2><b>");
  document.write("<a href=" + prefix + "index.html>home</a>");
  bullet();
  document.write("<a href=" + prefix + "contact.html>contact</a>");
  endline();
//  document.write("<a href=" + prefix + "research.html>research</a>");
//  bullet();
//  document.write("<a href=" + prefix + "courses.html>courses</a>");
//  endline();
  document.write("<a href=" + prefix + "papers.html>papers</a>");
  bullet();
  document.write("<a href=" + prefix + "talks.html>talks</a>");
  endline();
  document.write("<a href=" + prefix + "packages.html>packages</a>");
  bullet();
  document.write("<a href=" + prefix + "data.html>data</a>");
  endline();
  document.write("</font>");
}

function header(title, level) {
  document.write("<body bgcolor=white text=" + textcolor + " link=" + link + " alink=" + link + " vlink=" + link + " style=\"margin:0\" leftmargin=0 rightmargin=0 topmargin=0 bottommargin=0 marginwidth=0 marginheight=0>");
  if(title != "none") {
    document.write("<table width=100% border=0 bgcolor=" + headerbackground + "><tr>");
    document.write("<td><font size=1><br></font><font color=white size=6><b>&nbsp;" + title + "</b></font><font size=1><br>&nbsp;</font>");
    switch(level) {
      case 1: prefix = "../"; break;
      case 2: prefix = "../../"; break;
      default: prefix = ""; break;
    };
    toplinks(prefix);
    document.write("</table>");
  };
  document.write("<table width=100% cellspacing=10><tr><td>");
}

function footer() {
  document.write("</table>");
}
